"""Generic relation-composition certificates derived from typed proof plans."""
from __future__ import annotations

import itertools
from dataclasses import asdict, dataclass, replace

try:
    from .external_pre_fact_selector import select_unproduced_external_pre_facts
    from .node_authority_policy import node_authority_fingerprint
    from .parser import GoalIR, Node
    from .proof_compiler import CertificateStep, ProofPlan
    from .relation_certificate_models import (
        AddRelationCertificate,
        AttentionRelationCertificate,
        ChunkReconstructionCertificate,
        KVRelationStepCertificate,
        RMSNormRelationCertificate,
        RouterInputCheckpointCertificate,
        UnaryRelationCertificate,
        UnaryRelationChainCertificate,
        ZigzagAttentionKVRelationCertificate,
        ZigzagQRelationCertificate,
    )
except ImportError:
    from external_pre_fact_selector import select_unproduced_external_pre_facts
    from node_authority_policy import node_authority_fingerprint
    from parser import GoalIR, Node
    from proof_compiler import CertificateStep, ProofPlan
    from relation_certificate_models import (
        AddRelationCertificate,
        AttentionRelationCertificate,
        ChunkReconstructionCertificate,
        KVRelationStepCertificate,
        RMSNormRelationCertificate,
        RouterInputCheckpointCertificate,
        UnaryRelationCertificate,
        UnaryRelationChainCertificate,
        ZigzagAttentionKVRelationCertificate,
        ZigzagQRelationCertificate,
    )


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
class TransitionAuthorityRequirement:
    kind: str
    sides: tuple[str, ...]
    tids: tuple[int, ...]
    shape: tuple[int, ...] = ()
    length: int | None = None
    upper_bound: int | None = None


@dataclass(frozen=True)
class InnerChunkCEGatherCertificate:
    rule_id: str
    lean_theorem: str
    label_independence_theorem: str | None
    output_projection: str
    full_rows: int
    shard_rows: int
    input_step_triple: tuple[str, str, str]
    weight_binding: str
    label_binding: str
    weight_shape: tuple[int, ...]
    label_shape: tuple[int, ...]
    label_bound: int | None
    sm_ce_step: str
    pm_ce_steps: tuple[str, str]
    pm_gather_step: str
    label_chunk_step_triple: tuple[str, str, str] | None


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
    weight_binding = sm_ce.input_bindings[1]
    label_binding = sm_ce.input_bindings[2]
    if not weight_binding.startswith("init:") or any(
        step.input_bindings[1] != weight_binding for step in pm_ce
    ):
        raise RelationCompositionError("CE weight lacks one shared external InitGoal binding")
    if not label_binding.startswith("init:"):
        raise RelationCompositionError("CE full labels lack an external InitGoal binding")
    weight_tid = int(weight_binding.split(":", 1)[1])
    label_tid = int(label_binding.split(":", 1)[1])
    weight_lineage = ir.init_lineages.get(weight_tid)
    label_lineage = ir.init_lineages.get(label_tid)
    if weight_lineage is None or tuple(weight_lineage.tps) != ((0, weight_tid),):
        raise RelationCompositionError("CE weight lacks singleton InitGoal authority")
    if label_lineage is None or tuple(label_lineage.tps) != ((0, label_tid),):
        raise RelationCompositionError("CE labels lack singleton InitGoal authority")
    weight_shape = tuple(weight_lineage.tsShape)
    label_shape = tuple(label_lineage.tsShape)
    if tuple(sm_ce.input_shapes[1]) != weight_shape or tuple(sm_ce.input_shapes[2]) != label_shape:
        raise RelationCompositionError("CE weight/label shapes disagree with InitGoal authority")
    input_step_triple = tuple(
        _dependency_for_input(step, step.input_tids[0], by_id)
        for step in (sm_ce, *pm_ce)
    )
    if any(binding.startswith("init:") for binding in input_step_triple):
        raise RelationCompositionError("CE activation input relation is not produced")

    if len(ir.lineage.tsShape) != 1:
        raise RelationCompositionError("CE output lineage is not rank-1")
    full_rows = int(ir.lineage.tsShape[0])
    if full_rows <= 0 or full_rows % 2:
        raise RelationCompositionError("CE output rows do not split equally across two ranks")
    label_chunk_step_triple = None
    if projection == ".fst":
        label_steps = tuple(step.input_bindings[2] for step in pm_ce)
        if any(binding.startswith("init:") for binding in label_steps):
            raise RelationCompositionError("CE .fst local labels are not graph-produced chunks")
        try:
            chunks = tuple(by_id[binding] for binding in label_steps)
        except KeyError as exc:
            raise RelationCompositionError("CE .fst label chunk producer is absent") from exc
        if (tuple(step.op for step in chunks) != ("ChunkPrim", "ChunkPrim")
                or tuple(step.side for step in chunks) != ("pm", "pm")
                or tuple(step.rank for step in chunks) != (0, 1)
                or any(step.parameters != (0,) for step in chunks)
                or any(step.input_tids != (label_tid,) for step in chunks)
                or any(step.input_bindings != (label_binding,) for step in chunks)
                or any(step.output_shape != (full_rows // 2,) for step in chunks)):
            raise RelationCompositionError(
                "CE .fst local labels lack exact dim-0 ChunkPrim producer authority"
            )
        label_chunk_step_triple = (label_binding, *label_steps)
        theorem = (
            "TrainVerify.Denote.GeneratedPatterns."
            "fw_inner_chunk_ce_fst_allGather0_commute_2_of"
        )
        label_theorem = None
    else:
        theorem = "TrainVerify.Denote.fw_inner_chunk_ce_snd_allGatherDim0_shards"
        label_theorem = (
            "TrainVerify.Denote.RelationCompiler."
            "inner_chunk_ce_snd_labels_independent"
        )
    bound_contracts = [
        fact for fact in ir.tensor_value_bound_contracts
        if (fact.side, fact.tid, fact.length) == ("pm", label_tid, full_rows)
    ]
    if projection == ".fst":
        if len(bound_contracts) != 1 or bound_contracts[0].upper_bound != weight_shape[0]:
            raise RelationCompositionError(
                "CE .fst labels lack the exact public value-bound contract"
            )
        label_bound = bound_contracts[0].upper_bound
    else:
        label_bound = None
    return InnerChunkCEGatherCertificate(
        rule_id="inner-chunk-ce-projection-gather-two-rank",
        lean_theorem=theorem,
        label_independence_theorem=label_theorem,
        output_projection=projection,
        full_rows=full_rows,
        shard_rows=full_rows // 2,
        input_step_triple=input_step_triple,
        label_chunk_step_triple=label_chunk_step_triple,
        weight_binding=weight_binding,
        label_binding=label_binding,
        weight_shape=weight_shape,
        label_shape=label_shape,
        label_bound=label_bound,
        sm_ce_step=sm_ce.step_id,
        pm_ce_steps=(pm_ce[0].step_id, pm_ce[1].step_id),
        pm_gather_step=pm_gather.step_id,
    )


def is_inner_chunk_ce_projection_gather_topology(plan: ProofPlan) -> bool:
    """Recognize CE/AllGather topology before checking external authority."""
    if len(plan.target_steps) != 2:
        return False
    by_id = _step_map(plan)
    try:
        sm_ce = by_id[plan.target_steps[0]]
        pm_gather = by_id[plan.target_steps[1]]
        pm_inputs = tuple(by_id[step_id] for step_id in pm_gather.dependencies)
    except KeyError:
        return False
    return (
        sm_ce.side == "sm"
        and sm_ce.op == "FW_inner_chunk_ce"
        and sm_ce.output_projection in {".fst", ".snd"}
        and pm_gather.side == "pm"
        and pm_gather.op == "AllGatherPrim"
        and len(pm_inputs) >= 2
        and all(
            step.side == "pm"
            and step.op == "FW_inner_chunk_ce"
            and step.output_projection == sm_ce.output_projection
            for step in pm_inputs
        )
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


def _strip_multiref_alias(step: CertificateStep, by_id: dict[str, CertificateStep]) -> CertificateStep:
    if step.op != "FW_multiref" or len(step.dependencies) != 1:
        raise RelationCompositionError("expected a unary multiref alias")
    return by_id[step.dependencies[0]]


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
                if (expected_op != "FW_float" and
                        (tuple(steps[0].parameters) != full_out or
                         tuple(steps[1].parameters) != p0_out or
                         tuple(steps[2].parameters) != p1_out)):
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
class CP2ShardedToOrdinaryCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    lean_theorem: str


def advance_embedding_cp2_sharded_to_ordinary(plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("embedding CP2 adapter frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "ordinary" or len(frontier) != 3 or any(ref.startswith("init:") for ref in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            steps = tuple(by_id[ref] for ref in frontier)
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        operators = tuple(step.op for step in steps)
        if not (operators[0] == "FW_embedding"
                and operators[1:] == ("ReduceScatterPrim", "ReduceScatterPrim")):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        full_shape = tuple(steps[0].output_shape); shard_shape = tuple(steps[1].output_shape)
        if (tuple(steps[2].output_shape) != shard_shape or len(full_shape) != 2
                or full_shape != (shard_shape[0] * 2, shard_shape[1])):
            raise RelationCompositionError("embedding CP2 adapter shape contract fails")
        sharded = RelationFactSpec("sharded", tuple(frontier), gather_dim=0)
        ordinary = RelationFactSpec("ordinary", tuple(frontier))
        certificates.append(CP2ShardedToOrdinaryCertificate(
            rule_id="sharded-to-ordinary-cp2-embedding-reduce-scatter",
            input_fact=sharded, output_fact=ordinary,
            lean_theorem="TrainVerify.Denote.RelationCompiler.ShardedRel.toOrdinary2_dim0_rank2",
        ))
        rewritten.append(tuple(frontier)); rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class CP2OrdinaryToShardedCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    lean_theorem: str


def advance_attention_cp2_schema_adapters(plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("attention CP2 adapter frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) != 3 or any(ref.startswith("init:") for ref in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            steps = tuple(by_id[ref] for ref in frontier)
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        operators = tuple(step.op for step in steps)
        homogeneous = len(set(operators)) == 1 and operators[0] in {
            "FW_attn_sliding_window", "FW_reshape"
        }
        if not homogeneous:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        operator = operators[0]
        full_shape = tuple(steps[0].output_shape)
        shard_shape = tuple(steps[1].output_shape)
        if (tuple(steps[2].output_shape) != shard_shape or len(full_shape) != len(shard_shape)
                or full_shape != (shard_shape[0] * 2, *shard_shape[1:])
                or len(full_shape) not in {2, 3}):
            raise RelationCompositionError("CP2 schema adapter shape contract fails")
        theorem = (
            "TrainVerify.Denote.RelationCompiler.ShardedRel.ofOrdinary2_dim0_rank2"
            if len(full_shape) == 2 else
            "TrainVerify.Denote.RelationCompiler.ShardedRel.ofOrdinary2_dim0_rank3"
        )
        ordinary = RelationFactSpec("ordinary", tuple(frontier))
        sharded = RelationFactSpec("sharded", tuple(frontier), gather_dim=0)
        certificates.append(CP2OrdinaryToShardedCertificate(
            rule_id=f"ordinary-to-sharded-cp2-{operator.lower()}-output",
            input_fact=ordinary, output_fact=sharded,
            lean_theorem=theorem,
        ))
        rewritten.append(tuple(frontier)); rewritten_layouts.append("ordinary")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


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
            raise RelationCompositionError(
                f"attention operator/layout mismatch: operator={operator} layout={layout} "
                f"frontier={frontier} shapes={tuple(step.output_shape for step in steps)}"
            )
        if any(len(step.input_bindings) != 5 for step in steps):
            raise RelationCompositionError("attention signature does not expose Q/K/V plus metadata")
        metadata = tuple(steps[0].input_bindings[3:5])
        if any(tuple(step.input_bindings[3:5]) != metadata for step in steps[1:]):
            raise RelationCompositionError("attention metadata is not shared")
        raw_inputs = tuple(_produced_binding_triple(steps, index) for index in (0, 1, 2))
        if layout == "ordinary":
            inputs = raw_inputs
            input_layouts = ("ordinary", "ordinary", "ordinary")
        else:
            shared_kv = tuple(pair[1] == pair[2] for pair in raw_inputs[1:])
            if all(shared_kv):
                inputs = (
                    raw_inputs[0],
                    (raw_inputs[1][0], raw_inputs[1][1]),
                    (raw_inputs[2][0], raw_inputs[2][1]),
                )
                input_layouts = ("zigzag", "joined", "joined")
            elif not any(shared_kv):
                inputs = raw_inputs
                input_layouts = ("zigzag", "ordinary", "ordinary")
            else:
                raise RelationCompositionError(
                    "zigzag attention K/V mix shared and rank-sharded authority"
                )
        theorem = (
            "TrainVerify.Denote.GeneratedPatterns.applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair"
            if layout == "ordinary"
            else "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.attn_zigzag"
            if input_layouts[1:] == ("joined", "joined")
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
class ShardedFlattenToOrdinaryCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    writer_steps: tuple[str, str, str]
    input_shape: tuple[int, int, int]
    output_shape: tuple[int, int]
    lean_theorem: str


def advance_sharded_flatten_to_ordinary_frontiers(plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("sharded flatten frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) != 3 or any(ref.startswith("init:") for ref in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            steps = tuple(by_id[ref] for ref in frontier)
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if any(step.op != "FW_reshape" or len(step.input_bindings) != 1
               or len(step.input_shapes) != 1 for step in steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        source_full = tuple(steps[0].input_shapes[0])
        source_shard = tuple(steps[1].input_shapes[0])
        target_full = tuple(steps[0].output_shape)
        target_shard = tuple(steps[1].output_shape)
        if (tuple(steps[2].input_shapes[0]) != source_shard
                or tuple(steps[2].output_shape) != target_shard
                or len(source_full) != 3 or len(source_shard) != 3
                or source_full != (source_shard[0] * 2, source_shard[1], source_shard[2])
                or target_full != (source_full[0], source_full[1] * source_full[2])
                or target_shard != (source_shard[0], source_shard[1] * source_shard[2])
                or min(source_shard) <= 0):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        input_refs = _produced_binding_triple(steps, 0)
        certificates.append(ShardedFlattenToOrdinaryCertificate(
            rule_id="flatten-sharded-to-ordinary-two-rank-dim0",
            input_fact=RelationFactSpec("sharded", input_refs, gather_dim=0),
            output_fact=RelationFactSpec("ordinary", tuple(frontier)),
            writer_steps=tuple(frontier), input_shape=source_full,
            output_shape=target_full,
            lean_theorem="TrainVerify.Denote.RelationCompiler.ShardedRel.fw_view_3d_to_2d_ordinary_two",
        ))
        rewritten.append(input_refs); rewritten_layouts.append("sharded")
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
            rewritten.append(frontier)
            continue
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
    weight_bindings: tuple[str, str, str]
    weight_alias_steps: tuple[str, ...]
    weight_fact: RelationFactSpec
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
            rewritten.append(frontier)
            continue
        if any(len(step.input_bindings) != 2 or len(step.input_shapes) != 2 for step in steps):
            raise RelationCompositionError("linear signature is not data plus weight")
        weights = tuple(step.input_bindings[1] for step in steps)

        def weight_root(binding: str) -> tuple[str, tuple[str, ...]]:
            aliases = []
            current = binding
            seen = set()
            while not current.startswith("init:"):
                if current in seen or current not in by_id:
                    raise RelationCompositionError("linear weight alias chain is cyclic or missing")
                seen.add(current)
                alias = by_id[current]
                if (alias.op != "FW_multiref" or len(alias.input_bindings) != 1
                        or len(alias.parameters) != 1
                        or alias.output_index >= alias.parameters[0]):
                    raise RelationCompositionError(
                        f"linear weight is not an exact multiref alias: {current}"
                    )
                aliases.append(current)
                current = alias.input_bindings[0]
            return current, tuple(aliases)

        resolved_weights = tuple(weight_root(binding) for binding in weights)
        roots = tuple(item[0] for item in resolved_weights)
        if len(set(roots)) != 1:
            raise RelationCompositionError(
                f"linear weights have distinct semantic roots: frontier={frontier} weights={weights} roots={roots}"
            )
        weight_alias_steps = tuple(dict.fromkeys(
            alias for _, aliases in resolved_weights for alias in aliases
        ))
        for step in steps:
            data_shape, weight_shape = step.input_shapes
            output_shape = step.output_shape
            if len(data_shape) != 2 or len(weight_shape) != 2 or len(output_shape) != 2:
                raise RelationCompositionError("linear relation requires 2D tensors")
            if data_shape[1] != weight_shape[1] or output_shape != (data_shape[0], weight_shape[0]):
                raise RelationCompositionError("linear matrix dimensions disagree")
        input_triple = _produced_binding_triple(steps, 0)
        root = roots[0]
        if weights[0] != root or len(set(weights[1:])) != 1:
            raise RelationCompositionError("linear replicated weight bindings are not one exact joined value")
        weight_fact = RelationFactSpec("joined", (root,), joined_pm_step=weights[1])
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
            replicated_weight_tid=int(root.split(":", 1)[1]),
            weight_bindings=weights,
            weight_alias_steps=weight_alias_steps,
            weight_fact=weight_fact,
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
            rewritten.append(frontier)
            continue
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
            rewritten.append(frontier)
            continue
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
        if layout not in {"ordinary", "zigzag", "joined"}:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if any(len(step.input_bindings) != 2 for step in steps):
            raise RelationCompositionError("add signature is not binary")
        inputs = tuple(
            _produced_binding_triple(steps, index) for index in (0, 1)
        )
        theorem = (
            "TrainVerify.Denote.RelationCompiler.JoinedRel.add"
            if layout == "joined" else
            "TrainVerify.Denote.GeneratedPatterns.elemwiseAdd_allGather0_commute_cp2"
            if layout == "ordinary" else
            "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.add"
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
    weight_bindings: tuple[str, str, str]
    weight_alias_steps: tuple[str, ...]
    weight_fact: RelationFactSpec
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
        if layout not in {"ordinary", "zigzag", "joined", "joined_zigzag"}:
            rewritten.append(frontier)
            continue
        if any(len(step.input_bindings) != 2 for step in steps):
            raise RelationCompositionError("RMSNorm signature is not binary")
        weights = tuple(step.input_bindings[1] for step in steps)

        def weight_root(binding: str) -> tuple[str, tuple[str, ...]]:
            aliases = []
            current = binding
            seen = set()
            while not current.startswith("init:"):
                if current in seen or current not in by_id:
                    raise RelationCompositionError("RMSNorm weight alias chain is cyclic or missing")
                seen.add(current)
                alias = by_id[current]
                if (alias.op != "FW_multiref" or len(alias.input_bindings) != 1
                        or len(alias.parameters) != 1
                        or alias.output_index >= alias.parameters[0]):
                    raise RelationCompositionError(
                        f"RMSNorm weight is not an exact multiref alias: {current}"
                    )
                aliases.append(current)
                current = alias.input_bindings[0]
            return current, tuple(aliases)

        resolved_weights = tuple(weight_root(binding) for binding in weights)
        roots = tuple(item[0] for item in resolved_weights)
        if len(set(roots)) != 1:
            raise RelationCompositionError(
                f"RMSNorm weights have distinct semantic roots: {weights} -> {roots}"
            )
        weight_alias_steps = tuple(dict.fromkeys(
            alias for _, aliases in resolved_weights for alias in aliases
        ))
        input_triple = _produced_binding_triple(steps, 0)
        data_shapes = tuple(tuple(step.input_shapes[0]) for step in steps)
        weight_shapes = tuple(tuple(step.input_shapes[1]) for step in steps)
        if (any(tuple(step.output_shape) != data_shape
                for step, data_shape in zip(steps, data_shapes))
                or len(set(data_shapes[1:])) != 1
                or len(set(weight_shapes)) != 1):
            raise RelationCompositionError("RMSNorm data/weight shapes are inconsistent")
        full_shape, shard_shape = data_shapes[0], data_shapes[1]
        tensor_rank = len(full_shape)
        if (tensor_rank not in {2, 3}
                or any(len(shape) != tensor_rank for shape in data_shapes)
                or weight_shapes[0] != (full_shape[-1],)):
            raise RelationCompositionError(
                "RMSNorm relation shape contract is unsupported: "
                f"layout={layout} frontier={frontier} data_shapes={data_shapes} "
                f"weight_shapes={weight_shapes} outputs={tuple(step.output_shape for step in steps)}"
            )
        if layout in {"ordinary", "zigzag"}:
            if (len(steps) != 3 or data_shapes[1] != data_shapes[2]
                    or full_shape != (shard_shape[0] * 2, *shard_shape[1:])
                    or any(value <= 0 for shape in data_shapes for value in shape)):
                raise RelationCompositionError("RMSNorm CP2 shape contract is unsupported")
        elif len(steps) != 2 or any(shape != full_shape for shape in data_shapes[1:]):
            raise RelationCompositionError("RMSNorm joined shape contract is unsupported")
        elif layout == "joined_zigzag" and (
                full_shape[0] <= 0 or full_shape[0] % 2 != 0
                or any(value <= 0 for value in full_shape[1:])):
            raise RelationCompositionError("RMSNorm joined-zigzag theorem shape is unsupported")
        root = roots[0]
        if weights[0] != root or len(set(weights[1:])) != 1:
            raise RelationCompositionError("RMSNorm replicated weight bindings are not one exact joined value")
        weight_fact = RelationFactSpec("joined", (root,), joined_pm_step=weights[1])
        if layout == "ordinary":
            theorem = (
                "TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core"
                if tensor_rank == 2 else
                "TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core_3d"
            )
        else:
            if tensor_rank != 2:
                raise RelationCompositionError(
                    f"RMSNorm {layout} rank-{tensor_rank} theorem is not registered"
                )
            theorem = (
                "TrainVerify.Denote.RelationCompiler.JoinedRel.rms_norm"
                if layout == "joined" else
                "TrainVerify.Denote.RelationCompiler.JoinedZigzagRel.rms_norm"
                if layout == "joined_zigzag" else
                "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.rms_norm"
            )
        certificates.append(FrontierRMSNormCertificate(
            rule_id=f"rms-norm-{layout}-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            replicated_weight_tid=int(root.split(":", 1)[1]),
            weight_bindings=weights,
            weight_alias_steps=weight_alias_steps,
            weight_fact=weight_fact,
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
    output_indices: tuple[int, int, int]
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
        if layout not in {"ordinary", "zigzag", "joined", "joined_zigzag"}:
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
        arity = steps[0].parameters[0]
        if any(index >= arity for index in output_indices):
            raise RelationCompositionError("multiref output index exceeds arity")
        input_triple = tuple(step.input_bindings[0] for step in steps)
        certificates.append(MultirefAliasCertificate(
            rule_id="multiref-projection-alias",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            output_index=output_indices[0],
            output_indices=output_indices,
            arity=arity,
            lean_theorem=(
                "TrainVerify.Denote.fw_multiref_allGather0_commute_2"
                if len(set(output_indices)) == 1 else
                "TrainVerify.Denote.fw_multiref_allGather0_commute_2_indices"
            ),
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
            remaining.append(frontier)
            remaining_layouts.append(layout)
            continue
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
class InitAliasChunkCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_tid: int
    seed_pm_tid: int
    alias_steps: tuple[str, ...]
    chunk_steps: tuple[str, str]
    gather_dim: int
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    lean_theorem: str


def close_init_alias_chunk_boundaries(ir, plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("init-alias chunk frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates, remaining, remaining_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if (layout not in {"chunked", "sharded"} or len(frontier) != 3
                or not frontier[0].startswith("init:")
                or any(ref.startswith("init:") for ref in frontier[1:])):
            remaining.append(frontier); remaining_layouts.append(layout); continue
        chunk0, chunk1 = (by_id.get(ref) for ref in frontier[1:])
        if chunk0 is None or chunk1 is None or chunk0.op != "ChunkPrim" or chunk1.op != "ChunkPrim":
            remaining.append(frontier); remaining_layouts.append(layout); continue
        if ((chunk0.rank, chunk1.rank) != (0, 1)
                or len(chunk0.parameters) != 1 or chunk1.parameters != chunk0.parameters
                or chunk0.input_bindings != chunk1.input_bindings):
            raise RelationCompositionError("init-alias chunks are not one exact ordered pair")
        sm_tid = int(frontier[0].split(":", 1)[1])
        lineage = ir.init_lineages.get(sm_tid)
        if lineage is None:
            remaining.append(frontier); remaining_layouts.append(layout); continue
        pieces = tuple((int(rank), int(tid)) for rank, tid in lineage.tps)
        full_shape = tuple(int(value) for value in lineage.tsShape)
        lineage_shapes = tuple(tuple(int(value) for value in shape) for shape in lineage.tpShapes)
        if (lineage.ts != sm_tid or pieces != ((0, sm_tid),)
                or lineage.gatherDim is not None or lineage.replicated
                or lineage_shapes != (full_shape,)):
            remaining.append(frontier); remaining_layouts.append(layout); continue
        alias_steps = []
        alias_output_ref = chunk0.input_bindings[0]
        source = alias_output_ref
        while not source.startswith("init:"):
            alias = by_id.get(source)
            if alias is None or alias.op != "FW_multiref" or len(alias.input_bindings) != 1:
                raise RelationCompositionError("init-alias chunk source is not an exact multiref chain")
            if len(alias.parameters) != 1 or not 0 <= alias.output_index < alias.parameters[0]:
                raise RelationCompositionError("init-alias chunk multiref projection is malformed")
            if tuple(alias.input_shapes[0]) != tuple(alias.output_shape):
                raise RelationCompositionError("init-alias chunk multiref is not shape preserving")
            alias_steps.append(source); source = alias.input_bindings[0]
        if source != frontier[0]:
            raise RelationCompositionError("init-alias chunks do not derive from their SM lineage TID")
        gather_dim = int(chunk0.parameters[0])
        shard_shape = tuple(chunk0.output_shape)
        if (tuple(chunk1.output_shape) != shard_shape or gather_dim < 0
                or gather_dim >= len(shard_shape)):
            raise RelationCompositionError("init-alias chunk shard shapes or dimension disagree")
        reconstructed = list(shard_shape); reconstructed[gather_dim] *= 2
        if tuple(reconstructed) != full_shape:
            raise RelationCompositionError("init-alias chunks do not reconstruct the full lineage shape")
        output_fact = RelationFactSpec(layout, tuple(frontier), gather_dim=gather_dim)
        input_fact = RelationFactSpec(
            "joined", (frontier[0],), joined_pm_step=alias_output_ref
        )
        certificates.append(InitAliasChunkCertificate(
            rule_id=f"init-lineage-alias-chunks-two-rank-dim{gather_dim}",
            input_fact=input_fact, output_fact=output_fact,
            sm_tid=sm_tid, seed_pm_tid=sm_tid,
            alias_steps=tuple(alias_steps), chunk_steps=(chunk0.step_id, chunk1.step_id),
            gather_dim=gather_dim, full_shape=full_shape, shard_shape=shard_shape,
            lean_theorem=(
                "TrainVerify.Denote.RelationCompiler.ChunkedRel.of_chunks_two"
                if layout == "chunked" else
                "TrainVerify.Denote.RelationCompiler.ShardedRel.of_chunks_two"
            ),
        ))
    return tuple(certificates), tuple(remaining), tuple(remaining_layouts)


@dataclass(frozen=True)
class ZigzagFeatureLinearReductionCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_linear_step: str
    sm_output_identity_steps: tuple[str, ...]
    pm_linear_steps: tuple[str, str]
    pm_allreduce_step: str
    pm_output_identity_step: str
    pm_output_identity_writer_indices: tuple[int, int]
    pm_chunk_steps: tuple[str, str]
    full_weight_tid: int
    weight_shard_tids: tuple[int, int]
    rows: int
    input_features: int
    feature_features: int
    output_features: int
    lean_theorem: str


def advance_zigzag_feature_linear_reduction_boundaries(ir, plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("zigzag-feature reduction frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "zigzag" or len(frontier) != 3 or any(ref.startswith("init:") for ref in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_frontier, chunk0, chunk1 = (by_id[ref] for ref in frontier)
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if chunk0.op != "ChunkPrim" or chunk1.op != "ChunkPrim":
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if ((chunk0.rank, chunk1.rank) != (0, 1)
                or tuple(chunk0.parameters) != (0,) or tuple(chunk1.parameters) != (0,)
                or chunk0.input_bindings != chunk1.input_bindings):
            raise RelationCompositionError("zigzag-feature exit chunks are not one ordered dim-0 pair")
        sm_identity = []
        sm_ref = sm_frontier.step_id
        while sm_ref in by_id and by_id[sm_ref].op in {"FW_view", "FW_reshape", "FW_float", "FW_contiguous"}:
            step = by_id[sm_ref]
            if (len(step.input_bindings) != 1 or len(step.input_shapes) != 1
                    or tuple(step.input_shapes[0]) != tuple(step.output_shape)):
                break
            sm_identity.append(sm_ref); sm_ref = step.input_bindings[0]
        sm_linear = by_id.get(sm_ref)
        if sm_linear is None or sm_linear.op != "FW_mix_precision_linear":
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        pm_identity = []
        pm_ref = chunk0.input_bindings[0]
        while pm_ref in by_id and by_id[pm_ref].op in {"FW_view", "FW_reshape", "FW_float", "FW_contiguous"}:
            step = by_id[pm_ref]
            if (len(step.input_bindings) != 1 or len(step.input_shapes) != 1
                    or tuple(step.input_shapes[0]) != tuple(step.output_shape)):
                break
            pm_identity.append(pm_ref); pm_ref = step.input_bindings[0]
        allreduce = by_id.get(pm_ref)
        if (allreduce is None or allreduce.op != "AllReducePrim"
                or tuple(allreduce.parameters) not in {(), (0,)}
                or len(allreduce.input_bindings) != 2):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        pm_linears = tuple(by_id.get(ref) for ref in allreduce.input_bindings)
        if (any(step is None or step.op != "FW_mix_precision_linear" for step in pm_linears)
                or tuple(step.rank for step in pm_linears) != (0, 1)):
            raise RelationCompositionError("zigzag-feature exit local linears are malformed")
        if any(len(step.input_bindings) != 2 for step in (sm_linear, *pm_linears)):
            raise RelationCompositionError("zigzag-feature exit linear arity mismatch")
        activation_refs = (sm_linear.input_bindings[0],
                           pm_linears[0].input_bindings[0], pm_linears[1].input_bindings[0])
        sm_weight_ref = sm_linear.input_bindings[1]
        pm_weight_refs = tuple(step.input_bindings[1] for step in pm_linears)
        if not sm_weight_ref.startswith("init:") or any(not ref.startswith("init:") for ref in pm_weight_refs):
            raise RelationCompositionError("zigzag-feature exit weights lack exact InitGoal authority")
        full_weight_tid = int(sm_weight_ref.split(":", 1)[1])
        lineage = ir.init_lineages.get(full_weight_tid)
        if lineage is None:
            raise RelationCompositionError("zigzag-feature exit weight lineage is missing")
        weight_fact = init_lineage_relation_fact(lineage)
        if (weight_fact.layout != "sharded" or weight_fact.gather_dim != 1
                or weight_fact.step_triple != (sm_weight_ref, *pm_weight_refs)):
            raise RelationCompositionError("zigzag-feature exit weight lineage/order mismatch")
        full_input = tuple(sm_linear.input_shapes[0]); feature_input = tuple(pm_linears[0].input_shapes[0])
        full_weight = tuple(sm_linear.input_shapes[1]); shard_weight = tuple(pm_linears[0].input_shapes[1])
        full_output = tuple(sm_linear.output_shape); shard_output = tuple(chunk0.output_shape)
        if (len(full_input) != 2 or len(feature_input) != 2 or len(full_weight) != 2
                or len(shard_weight) != 2 or len(full_output) != 2 or len(shard_output) != 2
                or tuple(pm_linears[1].input_shapes[0]) != feature_input
                or tuple(pm_linears[1].input_shapes[1]) != shard_weight
                or full_input != (feature_input[0], feature_input[1] * 2)
                or full_weight != (shard_weight[0], shard_weight[1] * 2)
                or full_input[1] != full_weight[1]
                or full_output != (full_input[0], full_weight[0])
                or shard_output != (full_output[0] // 2, full_output[1])
                or min((*feature_input, *shard_weight, *shard_output)) <= 0):
            raise RelationCompositionError("zigzag-feature exit shape contract fails")
        if len(pm_identity) != 1:
            raise RelationCompositionError("zigzag-feature exit requires one exact PM identity output layer")
        pm_identity_step = by_id[pm_identity[0]]
        physical_indices = tuple(
            index for index, node in enumerate(ir.pm_nodes)
            if node.op == pm_identity_step.op and node.ins == [allreduce.output_tid]
            and node.outs == [pm_identity_step.output_tid]
            and node.rank in (0, 1)
        )
        if len(physical_indices) != 2 or tuple(ir.pm_nodes[index].rank for index in physical_indices) != (0, 1):
            raise RelationCompositionError("zigzag-feature exit physical identity writers are not exact CP2 ranks")
        input_fact = RelationFactSpec("zigzag_feature", activation_refs, gather_dim=1)
        output_fact = RelationFactSpec("zigzag", tuple(frontier))
        certificates.append(ZigzagFeatureLinearReductionCertificate(
            rule_id="zigzag-feature-linear-dim1-allreduce-chunks-cp2",
            input_fact=input_fact, weight_fact=weight_fact, output_fact=output_fact,
            sm_linear_step=sm_linear.step_id,
            sm_output_identity_steps=tuple(sm_identity),
            pm_linear_steps=tuple(step.step_id for step in pm_linears),
            pm_allreduce_step=allreduce.step_id,
            pm_output_identity_step=pm_identity_step.step_id,
            pm_output_identity_writer_indices=physical_indices,
            pm_chunk_steps=(chunk0.step_id, chunk1.step_id),
            full_weight_tid=full_weight_tid,
            weight_shard_tids=tuple(int(ref.split(":", 1)[1]) for ref in pm_weight_refs),
            rows=shard_output[0], input_features=full_input[1],
            feature_features=feature_input[1], output_features=full_output[1],
            lean_theorem="TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.mix_precision_linear_dim1_allReduce_chunks_cp2",
        ))
        rewritten.extend((activation_refs, weight_fact.step_triple))
        rewritten_layouts.extend(("zigzag_feature", "sharded"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class ReductionChunkBoundaryCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_identity_steps: tuple[str, ...]
    pm_allreduce_step: str
    pm_identity_steps: tuple[str, ...]
    pm_chunk_steps: tuple[str, str]
    lean_theorem: str


def advance_reduction_chunk_boundaries(plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("reduction-chunk frontier/layout arity mismatch")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    rewritten_layouts = []
    identity_ops = {"FW_view", "FW_reshape", "FW_float", "FW_contiguous"}
    for frontier, layout in zip(frontiers, layouts):
        if layout != "ordinary" or len(frontier) != 3 or any(ref.startswith("init:") for ref in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        sm_ref, chunk0_ref, chunk1_ref = frontier
        sm_current = sm_ref
        sm_identity = []
        while sm_current in by_id and by_id[sm_current].op in identity_ops:
            step = by_id[sm_current]
            if (len(step.input_bindings) != 1 or len(step.input_shapes) != 1
                    or tuple(step.input_shapes[0]) != tuple(step.output_shape)):
                break
            sm_identity.append(sm_current)
            sm_current = step.input_bindings[0]
        sm_linear = by_id.get(sm_current)
        chunk0, chunk1 = by_id.get(chunk0_ref), by_id.get(chunk1_ref)
        if (sm_linear is None or chunk0 is None or chunk1 is None
                or sm_linear.op not in {"FW_linear", "FW_mix_precision_linear"}
                or chunk0.op != "ChunkPrim" or chunk1.op != "ChunkPrim"):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if ((chunk0.rank, chunk1.rank) != (0, 1)
                or tuple(chunk0.parameters) != (0,) or tuple(chunk1.parameters) != (0,)
                or chunk0.input_bindings != chunk1.input_bindings
                or len(chunk0.input_bindings) != 1):
            raise RelationCompositionError("reduction-chunk output pair authority mismatch")
        pm_current = chunk0.input_bindings[0]
        pm_identity = []
        while pm_current in by_id and by_id[pm_current].op in identity_ops:
            step = by_id[pm_current]
            if (len(step.input_bindings) != 1 or len(step.input_shapes) != 1
                    or tuple(step.input_shapes[0]) != tuple(step.output_shape)):
                break
            pm_identity.append(pm_current)
            pm_current = step.input_bindings[0]
        reduce = by_id.get(pm_current)
        if reduce is None or reduce.op != "AllReducePrim" or int(reduce.rank) != 0:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        pm_linears = tuple(by_id.get(ref) for ref in reduce.input_bindings)
        if (not pm_linears or any(step is None for step in pm_linears)
                or any(step.op not in {"FW_linear", "FW_mix_precision_linear"} for step in pm_linears)
                or tuple(int(step.rank) for step in pm_linears) != tuple(range(len(pm_linears)))):
            raise RelationCompositionError("reduction-chunk contributions are not ordered linear writers")
        full_shape = tuple(sm_linear.output_shape)
        if (len(full_shape) != 2 or any(tuple(step.output_shape) != full_shape for step in pm_linears)
                or tuple(reduce.output_shape) != full_shape
                or tuple(chunk0.input_shapes[0]) != full_shape
                or tuple(chunk1.input_shapes[0]) != full_shape
                or tuple(chunk0.output_shape) != tuple(chunk1.output_shape)
                or full_shape != (2 * chunk0.output_shape[0], chunk0.output_shape[1])):
            raise RelationCompositionError("reduction-chunk shape authority mismatch")
        input_fact = RelationFactSpec("reduction", (sm_current, *tuple(reduce.input_bindings)))
        output_fact = RelationFactSpec("ordinary", frontier)
        certificates.append(ReductionChunkBoundaryCertificate(
            rule_id="reduction-allreduce-chunks-ordinary-two-rank",
            input_fact=input_fact,
            output_fact=output_fact,
            sm_identity_steps=tuple(sm_identity),
            pm_allreduce_step=pm_current,
            pm_identity_steps=tuple(pm_identity),
            pm_chunk_steps=(chunk0_ref, chunk1_ref),
            lean_theorem="TrainVerify.Denote.RelationCompiler.ReductionRel.to_ordinary_chunks_2d",
        ))
        rewritten.append(input_fact.step_triple)
        rewritten_layouts.append("reduction")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


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
    sm_output_identity_chain: tuple[str, ...]
    pm_output_identity_chain: tuple[str, ...]
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
        "FW_mix_precision_linear": (
            "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.mix_precision_linear",
            "TrainVerify.Denote.RelationCompiler.allGather0_reconstruct_chunks_2d",
        ),
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
        if any(binding.startswith("init:") for binding in frontier) or len(frontier) != 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        sm_frontier, chunk0, chunk1 = (by_id[binding] for binding in frontier)
        if chunk0.op != "ChunkPrim" or chunk1.op != "ChunkPrim":
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        sm_binding = frontier[0]
        sm_output_identity_chain = []
        while sm_binding in by_id and by_id[sm_binding].op not in supported:
            candidate = by_id[sm_binding]
            if (candidate.op not in {"FW_view", "FW_reshape", "FW_float", "FW_contiguous"}
                    or len(candidate.input_bindings) != 1
                    or len(candidate.input_shapes) != 1
                    or candidate.input_shapes[0] != candidate.output_shape):
                break
            sm_output_identity_chain.append(sm_binding)
            sm_binding = candidate.input_bindings[0]
        if sm_binding not in by_id or by_id[sm_binding].op not in supported:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        sm_step = by_id[sm_binding]
        if layout not in {"ordinary", "zigzag"}:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if layout == "zigzag" and sm_step.op == "FW_mix_precision_linear":
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if layout == "zigzag" and sm_step.op not in {
            "FW_norm_linear", "FW_per_head_mix_precision_linear"
        }:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if goal_ir is None:
            raise RelationCompositionError("full-producer chunk relation lacks GoalIR lineage authority")
        if (chunk0.rank, chunk1.rank) != (0, 1) or chunk0.parameters != (0,) or chunk1.parameters != (0,):
            raise RelationCompositionError("full-producer chunk pair has malformed rank or dimension")
        if len(chunk0.input_bindings) != 1 or chunk1.input_bindings != chunk0.input_bindings:
            raise RelationCompositionError("full-producer chunks do not share one prior producer")
        pm_frontier_binding = chunk0.input_bindings[0]
        pm_binding = pm_frontier_binding
        pm_output_identity_chain = []
        while pm_binding in by_id and by_id[pm_binding].op not in supported:
            candidate = by_id[pm_binding]
            if (candidate.op not in {"FW_view", "FW_reshape", "FW_float", "FW_contiguous"}
                    or len(candidate.input_bindings) != 1
                    or len(candidate.input_shapes) != 1
                    or candidate.input_shapes[0] != candidate.output_shape):
                break
            pm_output_identity_chain.append(pm_binding)
            pm_binding = candidate.input_bindings[0]
        if pm_binding.startswith("init:") or pm_binding not in by_id:
            raise RelationCompositionError("full-producer chunk source is not a typed prior step")
        pm_full_binding = pm_binding
        pm_full = by_id[pm_full_binding]
        if pm_full.op != sm_step.op or pm_full.denote_fn != sm_step.denote_fn or pm_full.parameters != sm_step.parameters:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
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
        if sm_step.op == "FW_mix_precision_linear":
            result_theorem = (
                "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.mix_precision_linear_fullProducer_chunks"
            )
        else:
            result_theorem = (
                "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.per_head_linear_fullProducer_chunks"
                if sm_step.op == "FW_per_head_mix_precision_linear"
                else "TrainVerify.Denote.RelationCompiler.Ordinary2Rel.norm_linear_fullProducer_chunks"
            )
        if layout == "zigzag" and sm_step.op == "FW_per_head_mix_precision_linear":
            operator_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.per_head_linear"
            reconstruction_theorem = "TrainVerify.Denote.GeneratedPatterns.chunk_allGather_cp2_dim0_3d"
            result_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.per_head_linear_fullProducer_chunks"
        elif layout == "zigzag" and sm_step.op == "FW_mix_precision_linear":
            operator_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.mix_precision_linear"
            reconstruction_theorem = "TrainVerify.Denote.GeneratedPatterns.chunk_allGather_cp2_dim0_2d"
            result_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.mix_precision_linear_fullProducer_chunks"
        elif layout == "zigzag":
            operator_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.norm_linear"
            reconstruction_theorem = "TrainVerify.Denote.GeneratedPatterns.chunk_allGather_cp2_dim0_2d"
            result_theorem = "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.norm_linear_fullProducer_chunks"
        certificates.append(FullProducerChunkCertificate(
            rule_id=f"{sm_step.op}-full-producer-chunks-{layout}-two-rank",
            operator=sm_step.op, relation_kind=layout, output_step_triple=frontier,
            pre_layout=layout, post_layout=layout,
            sm_operator_step=sm_binding, pm_full_operator_step=pm_full_binding,
            pm_chunk_steps=(frontier[1], frontier[2]), sm_identity_chain=tuple(sm_identity_chain),
            pm_identity_chain=tuple(identity_chain),
            sm_output_identity_chain=tuple(sm_output_identity_chain),
            pm_output_identity_chain=tuple(pm_output_identity_chain),
            pm_allgather_step=current, input_step_triple=input_triple,
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
            else:
                alias_classes = [
                    item for item in ir.pm_input_value_classes if tid in item.tids
                ]
                if len(alias_classes) == 1:
                    source = alias_classes[0]
                    contract_aliases = [
                        candidate for candidate in contracts
                        if candidate[0] == "pm" and candidate[2:] == (condition.upper, 2)
                        and candidate[1] in source.tids
                    ]
                    if len(contract_aliases) == 1:
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
    synchronized_steps: tuple[SynchronizedRelationStep, ...] = (),
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

    for step in synchronized_steps:
        if step.rule_id == "zigzag-topk-unshuffle-two-rank":
            add_seed(step.input_step_triple, f"init:{step.metadata_tid}")

    for cert in certificates:
        output = getattr(cert, "output_step_triple", None)
        if isinstance(cert, (FaithfulShuffleCertificate, KRankShuffleEntryCertificate)):
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
class KRankShuffleEntryCertificate:
    rule_id: str
    op: str
    output_step_triple: tuple[str, ...]
    input_step_triple: tuple[str, ...]
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
    lean_theorem: str = "TrainVerify.Denote.RelationCompiler.ZigzagKRel.of_sharded"
    pre_layout: str = "sharded"
    post_layout: str = "zigzag_k"

    @property
    def input_fact(self):
        return RelationFactSpec("sharded", self.input_step_triple, gather_dim=0)

    @property
    def output_fact(self):
        return RelationFactSpec("zigzag_k", self.output_step_triple)


def advance_k_rank_shuffle_entry_frontiers(ir, plan, frontiers, layouts):
    """Exact homogeneous entry only; semantic rank order is never node-index sorted."""
    from .ordered_buddy_authority_policy import OrderedBuddyRow, check_ordered_cp_buddy_authority
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K shuffle frontier/layout arity mismatch")
    by_id = _step_map(plan)
    certificates, remaining, kinds = [], [], []
    def require(ok, message):
        if not ok:
            raise RelationCompositionError("K shuffle " + message)
    for frontier, layout in zip(frontiers, layouts):
        if layout != "zigzag_k":
            remaining.append(frontier); kinds.append(layout); continue
        require(plan.supported, "requires supported graph authority")
        require(len(frontier) == ir.pm_num_ranks + 1 and ir.pm_num_ranks > 0
                and ir.sm_num_ranks == 1, "rank count mismatch")
        require(len(set(frontier)) == len(frontier) and all(ref in by_id for ref in frontier),
                "missing or duplicate writer")
        steps = tuple(by_id[ref] for ref in frontier)
        k = ir.pm_num_ranks
        op = steps[0].op
        require(op in {"FW_maybe_shuffle", "BW_maybe_unshuffle"}
                and all(s.op == op for s in steps), "requires homogeneous entry writers")
        require(tuple((s.side, s.rank) for s in steps) == (("sm", 0),) + tuple(("pm", r) for r in range(k)), "rank order mismatch")
        require(tuple(s.parameters for s in steps) == ((1, 0),) + tuple((k,r) for r in range(k)), "parameters mismatch")
        require(all(len(s.input_tids) == len(s.input_bindings) == len(s.input_shapes) == 2 for s in steps), "signature mismatch")
        # Bind every step back to the actual graph, including producer identity.
        for step in steps:
            nodes = ir.sm_nodes if step.side == "sm" else ir.pm_nodes
            require(0 <= step.node_index < len(nodes), "missing graph writer")
            node = nodes[step.node_index]
            require((node.rank, node.op, tuple(node.ins), tuple(node.outs), tuple(node.params or ())) ==
                    (step.rank, step.op, step.input_tids, (step.output_tid,), step.parameters), "graph writer mismatch")
        for groups, side_steps in ((ir.sm_replica_groups, steps[:1]), (ir.pm_replica_groups, steps[1:])):
            expected = tuple((s.rank, s.output_tid) for s in side_steps)
            matches = [g for g in groups if any((m.rank,m.primary_out_tid) in expected for m in g.members)]
            require(len(matches) == 1 and tuple((m.rank,m.primary_out_tid) for m in matches[0].members) == expected,
                    "requires explicit ordered buddy groups")
            require(matches[0].irname.rsplit(".",1)[-1] in {op, "wrap_" + op[3:]}, "buddy operator mismatch")
        if k > 1:
            decision = check_ordered_cp_buddy_authority(tuple(OrderedBuddyRow(s.node_index, s.op, s.parameters, s.input_tids) for s in steps[1:]), cp_size=k, expected_op=op)
            require(decision.failure is None, "ordered buddy policy rejected authority")
        tid = steps[0].input_tids[1]
        require(all(s.input_tids[1] == tid and s.input_bindings[1] == f"init:{tid}" and s.input_shapes[1] == (2,) for s in steps), "metadata binding mismatch")
        lineage = ir.init_lineages.get(tid)
        require(lineage is not None and lineage.ts == tid and tuple(lineage.tps) == ((0,tid),)
                and tuple(lineage.tsShape) == (2,) and tuple(map(tuple,lineage.tpShapes)) == ((2,),)
                and lineage.gatherDim is None and not lineage.replicated, "metadata singleton lineage mismatch")
        classes = []
        for values in (ir.sm_input_value_classes, ir.pm_input_value_classes):
            found = [c for c in values if tid in c.tids]
            require(len(found) == 1, "metadata value class missing or ambiguous")
            classes.append(found[0])
        require(classes[0].source == classes[1].source, "metadata cross-class mismatch")
        full, shard = steps[0].input_shapes[0], steps[1].input_shapes[0]
        require(bool(shard) and full == (k*shard[0], *shard[1:]) and all(d > 0 for d in (*full,*shard)), "shape split mismatch")
        require(all(s.input_shapes[0] == shard and s.output_shape == shard for s in steps[1:]) and steps[0].output_shape == full, "input/output shapes mismatch")
        contracts = [c for c in ir.packed_cu_contracts if c.side == "pm" and c.tid in classes[1].tids]
        require(bool(contracts) and all((c.total_tokens,c.num_ranks) == (full[0],k) for c in contracts), "packed authority token/rank mismatch")
        contract = contracts[0]
        inputs = tuple(s.input_bindings[0] for s in steps)
        # Verify bindings, not merely TIDs or shapes, against authentic producer planning.
        from .proof_compiler import compile_proof_plan, build_default_registry
        authentic = compile_proof_plan(ir, build_default_registry())
        authentic_steps = _step_map(authentic)
        require(authentic.supported and all(authentic_steps.get(s.step_id) == s for s in steps), "input producer authority mismatch")
        certificates.append(KRankShuffleEntryCertificate(
            "fw-shuffle-sharded-to-zigzag-k" if op == "FW_maybe_shuffle" else "bw-unshuffle-sharded-to-zigzag-k",
            op, frontier, inputs, tid, contract.tid, classes[1].source, ((0,tid),),
            full[0], k, ((0,steps[0].output_tid),), tuple((s.rank,s.output_tid) for s in steps[1:]), full, shard))
        remaining.append(inputs); kinds.append("sharded")
    return tuple(certificates), tuple(remaining), tuple(kinds)


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
        # Legacy generated authorities predate the optional replicaGroups field.
        # In that all-or-nothing case the synchronized shuffle frontier itself is
        # the pinned membership authority; never use this fallback for a partial
        # or conflicting replica-group declaration.
        if not groups:
            return None, expected
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
        if {step.op for step in steps} not in ({"FW_maybe_shuffle"}, {"BW_maybe_unshuffle"}):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if ir.sm_num_ranks != 1 or ir.pm_num_ranks != 2:
            raise RelationCompositionError("faithful shuffle requires exact SM=1/PM=2 graph ranks")
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
            rule_id=("faithful-maybe-shuffle-ordinary-to-zigzag-two-rank"
                     if steps[0].op == "FW_maybe_shuffle"
                     else "bw-maybe-unshuffle-ordinary-to-zigzag-two-rank"),
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
        step_ops = {step.op for step in steps}
        if step_ops not in ({"FW_maybe_unshuffle"}, {"BW_maybe_shuffle"}):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if layout != "ordinary":
            raise RelationCompositionError("unshuffle-family output must be ordinary")
        op = steps[0].op
        full, rank0, rank1 = steps
        if full.parameters != (1, 0):
            raise RelationCompositionError("two-rank unshuffle parameters are malformed")
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
                    index,
                    step.op,
                    tuple(step.parameters),
                    tuple(step.input_bindings),
                )
                for index, step in enumerate((rank0, rank1))
            ),
            cp_size=2,
            expected_op=op,
        )
        if decision.failure in {
            OrderedBuddyFailure.INVALID_CP_SIZE,
            OrderedBuddyFailure.INCOMPLETE,
            OrderedBuddyFailure.OUT_OF_ORDER,
            OrderedBuddyFailure.OP_MISMATCH,
            OrderedBuddyFailure.PARAMETER_MISMATCH,
            OrderedBuddyFailure.CURRENT_NODE_MISMATCH,
        }:
            raise RelationCompositionError("two-rank unshuffle parameters are malformed")
        if any(
            len(step.input_bindings) != 2 or len(step.input_shapes) != 2
            for step in steps
        ):
            raise RelationCompositionError("two-rank unshuffle signature mismatch")
        if decision.failure in {
            OrderedBuddyFailure.SIGNATURE_MISMATCH,
            OrderedBuddyFailure.UNIFORM_SIGNATURE_MISMATCH,
        }:
            raise RelationCompositionError("two-rank unshuffle signature mismatch")
        if decision.failure is OrderedBuddyFailure.METADATA_MISMATCH:
            raise RelationCompositionError("unshuffle metadata is not one shared external input")
        metadata = tuple(step.input_bindings[1] for step in steps)
        if metadata[0] != metadata[1] or not metadata[0].startswith("init:"):
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
            rule_id=("zigzag-to-ordinary-unshuffle-two-rank" if op == "FW_maybe_unshuffle"
                     else "bw-maybe-shuffle-zigzag-to-ordinary-two-rank"),
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
        certificate_common = {
            "relation_kind": layout, "output_step_triple": frontier,
            "input_step_triples": tuple(inputs), "full_weight_bindings": full_weight_bindings,
            "shard_weight_bindings": ((rank0_weights[0], rank0_weights[1]), (rank0_weights[2], rank0_weights[3])),
            "num_experts": num_exp, "expert_split": expert_split, "top_k": top_k,
        }
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
    arities = {"FW_sigmoid": 1, "FW_swiglu": 2, "FW_glu": 2}
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
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
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
            ordinary_name = {
                "FW_sigmoid": "sigmoid",
                "FW_swiglu": "swiglu",
                "FW_glu": "glu",
            }[operator]
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
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
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
        if layout not in {"ordinary", "zigzag"}:
            rewritten.append(frontier)
            continue
        if any(len(step.input_shapes) != 1 or step.input_shapes[0] != step.output_shape for step in steps):
            raise RelationCompositionError("FW_to is not shape-preserving")
        if steps[0].output_shape[0] != steps[1].output_shape[0] + steps[2].output_shape[0]:
            raise RelationCompositionError(
                f"FW_to shards do not reconstruct full rows: frontier={frontier} "
                f"shapes={tuple(step.output_shape for step in steps)} layout={layout}"
            )
        if steps[1].output_shape != steps[2].output_shape:
            raise RelationCompositionError("FW_to shard shapes disagree")
        input_triple = _produced_binding_triple(steps, 0)
        certificates.append(FrontierToCertificate(
            rule_id=f"to-{layout}-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_step_triple=input_triple,
            input_shape=steps[0].input_shapes[0],
            output_shape=steps[0].output_shape,
            lean_theorem=(
                "TrainVerify.Denote.fw_to_allGather0_commute_2"
                if layout == "ordinary" else
                "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.fw_to"
            ),
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
        if layout in {"joined", "joined_zigzag"}:
            if len(frontier) != 2 or len(steps) != 2:
                raise RelationCompositionError(f"{layout} per-head linear requires one SM and one PM writer")
            sm_step, pm_step = steps
            if (sm_step.side, pm_step.side) != ("sm", "pm"):
                raise RelationCompositionError("joined-zigzag per-head linear side authority mismatch")
            if any(len(step.input_shapes) != 2 or len(step.input_bindings) != 2 for step in steps):
                raise RelationCompositionError("joined-zigzag per-head linear signature mismatch")
            data_shape, weight_shape = sm_step.input_shapes
            if (tuple(pm_step.input_shapes[0]) != tuple(data_shape)
                    or tuple(pm_step.input_shapes[1]) != tuple(weight_shape)
                    or len(data_shape) != 2 or len(weight_shape) != 3
                    or weight_shape[2] != data_shape[1]
                    or tuple(sm_step.output_shape) != tuple(pm_step.output_shape)
                    or tuple(sm_step.output_shape) != (data_shape[0], weight_shape[0], weight_shape[1])):
                raise RelationCompositionError("joined-zigzag per-head linear shape authority mismatch")
            weight_bindings = tuple(step.input_bindings[1] for step in steps)
            if len(set(weight_bindings)) != 1 or not weight_bindings[0].startswith("init:"):
                raise RelationCompositionError("joined-zigzag per-head linear weight is not replicated")
            input_pair = (sm_step.input_bindings[0], pm_step.input_bindings[0])
            certificates.append(PerHeadLinearRelationCertificate(
                rule_id=f"per-head-linear-{layout}",
                relation_kind=layout,
                output_step_triple=frontier,
                input_role="activation",
                input_relation_step_triple=input_pair,
                replicated_weight_tid=int(weight_bindings[0].split(":", 1)[1]),
                lean_theorem=(
                    "TrainVerify.Denote.RelationCompiler.JoinedRel.per_head_linear"
                    if layout == "joined" else
                    "TrainVerify.Denote.RelationCompiler.JoinedZigzagRel.per_head_linear"
                ),
            ))
            rewritten.append(input_pair)
            continue
        if layout not in {"ordinary", "zigzag", "sharded"}:
            rewritten.append(frontier)
            continue
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
            rule_id=f"per-head-linear-{layout}-two-rank",
            relation_kind=layout,
            output_step_triple=frontier,
            input_role="activation",
            input_relation_step_triple=input_triple,
            replicated_weight_tid=int(weight_bindings[0].split(":", 1)[1]),
            lean_theorem=(
                "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_per_head_linear_dim0_two"
                if layout == "sharded" else
                "TrainVerify.Denote.fw_per_head_mix_precision_linear_allGather0_commute_2"
                if layout == "ordinary" else
                "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.per_head_linear"
            ),
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


@dataclass(frozen=True)
class KRankSumAllReduceTerminalCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    input_fact: RelationFactSpec
    sm_sum_step: str
    pm_sum_steps: tuple[str, ...]
    pm_allreduce_step: str
    lean_theorem: str


def match_sum_allreduce_k_rank(
    ir: GoalIR,
    plan: ProofPlan,
) -> KRankSumAllReduceTerminalCertificate:
    if int(ir.sm_num_ranks) != 1 or int(ir.pm_num_ranks) < 2:
        raise RelationCompositionError("K-rank sum/AllReduce terminal requires SM=1 and PM>=2")
    if len(plan.target_steps) != 2:
        raise RelationCompositionError("K-rank sum/AllReduce terminal requires exactly two target steps")
    by_id = {step.step_id: step for step in plan.steps}
    try:
        targets = [by_id[ref] for ref in plan.target_steps]
    except KeyError as exc:
        raise RelationCompositionError(f"terminal target step is unresolved: {exc.args[0]}") from exc
    sm_targets = [step for step in targets if step.side == "sm"]
    pm_targets = [step for step in targets if step.side == "pm"]
    if len(sm_targets) != 1 or len(pm_targets) != 1:
        raise RelationCompositionError("K-rank sum/AllReduce terminal requires one SM and one PM target")
    sm_sum, pm_reduce = sm_targets[0], pm_targets[0]
    if sm_sum.op != "FW_sum" or pm_reduce.op != "AllReducePrim" or int(pm_reduce.rank) != 0:
        raise RelationCompositionError("terminal is not SM FW_sum against rank-0 PM AllReducePrim")
    k = int(ir.pm_num_ranks)
    if len(sm_sum.input_bindings) != 1 or len(pm_reduce.input_bindings) != k:
        raise RelationCompositionError("sum/AllReduce terminal input arity does not match rank count")
    try:
        pm_sums = tuple(by_id[ref] for ref in pm_reduce.input_bindings)
        sm_input = by_id[sm_sum.input_bindings[0]]
    except KeyError as exc:
        raise RelationCompositionError(f"sum/AllReduce dependency is unresolved: {exc.args[0]}") from exc
    if any(step.side != "pm" or step.op != "FW_sum" for step in pm_sums):
        raise RelationCompositionError("AllReduce inputs are not PM FW_sum writers")
    if tuple(int(step.rank) for step in pm_sums) != tuple(range(k)):
        raise RelationCompositionError("PM FW_sum writers are not ordered ranks 0..K-1")
    if any(len(step.input_bindings) != 1 for step in pm_sums):
        raise RelationCompositionError("PM FW_sum writer must have exactly one input")
    if any(tuple(step.output_shape) != tuple(sm_sum.output_shape) for step in pm_sums):
        raise RelationCompositionError("local and full FW_sum output shapes disagree")
    if tuple(pm_reduce.output_shape) != tuple(sm_sum.output_shape):
        raise RelationCompositionError("AllReduce and SM FW_sum output shapes disagree")
    try:
        pm_inputs = tuple(by_id[step.input_bindings[0]] for step in pm_sums)
    except KeyError as exc:
        raise RelationCompositionError(f"local FW_sum input is unresolved: {exc.args[0]}") from exc
    if any(step.side != "pm" for step in pm_inputs) or sm_input.side != "sm":
        raise RelationCompositionError("sum/AllReduce source frontier has the wrong side")
    shard_shape = tuple(pm_inputs[0].output_shape)
    if any(tuple(step.output_shape) != shard_shape for step in pm_inputs):
        raise RelationCompositionError("sum/AllReduce source PM shard shapes disagree")
    full_shape = tuple(sm_input.output_shape)
    if len(full_shape) != len(shard_shape):
        raise RelationCompositionError("sum/AllReduce full and shard ranks disagree")
    candidates = [
        dim for dim in range(len(full_shape))
        if full_shape[dim] == shard_shape[dim] * k
        and all(full_shape[i] == shard_shape[i] for i in range(len(full_shape)) if i != dim)
    ]
    if len(candidates) != 1:
        raise RelationCompositionError(
            f"sum/AllReduce source does not determine one gather dimension: {candidates}"
        )
    gather_dim = candidates[0]
    return KRankSumAllReduceTerminalCertificate(
        rule_id="sum-allreduce-k-rank",
        rank_count=k,
        gather_dim=gather_dim,
        input_fact=RelationFactSpec(
            "sharded",
            (sm_input.step_id, *(step.step_id for step in pm_inputs)),
            gather_dim=gather_dim,
        ),
        sm_sum_step=sm_sum.step_id,
        pm_sum_steps=tuple(step.step_id for step in pm_sums),
        pm_allreduce_step=pm_reduce.step_id,
        lean_theorem="TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum",
    )


@dataclass(frozen=True)
class KRankSumProducerCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_sum_step: str
    pm_sum_steps: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_sum_producer_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankSumProducerCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Decompose an exact FW_sum ReductionRel into its shape-derived ShardedRel input."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank sum producer frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates: list[KRankSumProducerCertificate] = []
    rewritten: list[tuple[str, ...]] = []
    rewritten_layouts: list[str] = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "reduction" or len(frontier) < 2:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        try:
            sm_sum = by_id[frontier[0]]
            pm_sums = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if sm_sum.side != "sm" or sm_sum.op != "FW_sum":
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if any(step.side != "pm" or step.op != "FW_sum" for step in pm_sums):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        rank_count = len(pm_sums)
        if int(sm_sum.rank) != 0:
            raise RelationCompositionError("K-rank sum producer SM writer must have rank zero")
        if tuple(int(step.rank) for step in pm_sums) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank sum producer PM writers are not exact ordered ranks")
        if tuple(getattr(sm_sum, "parameters", ())) != () or any(
            tuple(getattr(step, "parameters", ())) != () for step in pm_sums
        ):
            raise RelationCompositionError("K-rank FW_sum producer writers must declare no parameters")
        if len(sm_sum.input_bindings) != 1 or any(
            len(step.input_bindings) != 1 for step in pm_sums
        ):
            raise RelationCompositionError("K-rank FW_sum producer writer input arity mismatch")
        if tuple(sm_sum.output_shape) != (1,) or any(
            tuple(step.output_shape) != (1,) for step in pm_sums
        ):
            raise RelationCompositionError("K-rank FW_sum producer outputs must have exact shape [1]")
        try:
            sm_input = by_id[sm_sum.input_bindings[0]]
            pm_inputs = tuple(by_id[step.input_bindings[0]] for step in pm_sums)
        except KeyError as exc:
            raise RelationCompositionError("K-rank FW_sum producer input writer is unresolved") from exc
        if sm_input.side != "sm" or any(step.side != "pm" for step in pm_inputs):
            raise RelationCompositionError("K-rank FW_sum producer inputs have wrong-side writers")
        if tuple(int(step.rank) for step in pm_inputs) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank FW_sum producer input shards are not exact ordered ranks")
        full_shape = tuple(sm_input.output_shape)
        shard_shapes = tuple(tuple(step.output_shape) for step in pm_inputs)
        if not shard_shapes or any(shape != shard_shapes[0] for shape in shard_shapes[1:]):
            raise RelationCompositionError("K-rank FW_sum producer input shard shapes disagree")
        shard_shape = shard_shapes[0]
        candidates = [
            dim for dim in range(len(full_shape))
            if full_shape[dim] == shard_shape[dim] * rank_count
            and all(full_shape[index] == shard_shape[index]
                    for index in range(len(full_shape)) if index != dim)
        ]
        if len(candidates) != 1:
            raise RelationCompositionError(
                f"K-rank FW_sum producer input does not determine one sharding axis: {candidates}"
            )
        gather_dim = candidates[0]
        declared_sm = tuple(tuple(shape) for shape in getattr(sm_sum, "input_shapes", ()))
        declared_pm = tuple(
            tuple(tuple(shape) for shape in getattr(step, "input_shapes", ()))
            for step in pm_sums
        )
        if declared_sm != (full_shape,) or declared_pm != tuple((shape,) for shape in shard_shapes):
            raise RelationCompositionError("K-rank FW_sum producer declared input shapes disagree with writers")
        if shard_shape[gather_dim] <= 0:
            raise RelationCompositionError("K-rank FW_sum producer gather extent must be positive")
        post_stride = 1
        for extent in shard_shape[gather_dim + 1:]:
            post_stride *= extent
        if post_stride <= 0:
            raise RelationCompositionError("K-rank FW_sum producer post-stride must be positive")
        input_fact = RelationFactSpec(
            "sharded", (sm_input.step_id, *(step.step_id for step in pm_inputs)),
            gather_dim=gather_dim,
        )
        output_fact = RelationFactSpec("reduction", tuple(frontier))
        spec = get_closed_rule_spec("sum-producer-sharded-k-rank-dim1")
        certificates.append(KRankSumProducerCertificate(
            rule_id=spec.rule_id,
            rank_count=rank_count,
            gather_dim=gather_dim,
            full_shape=full_shape,
            shard_shape=shard_shape,
            input_fact=input_fact,
            output_fact=output_fact,
            sm_sum_step=sm_sum.step_id,
            pm_sum_steps=tuple(step.step_id for step in pm_sums),
            lean_theorem=spec.lean_theorems[0],
        ))
        rewritten.append(input_fact.step_triple)
        rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankVocabShardedEmbeddingProducerCertificate:
    rule_id: str
    rank_count: int
    ids_tid: int
    shard_rows: int
    hidden_size: int
    ids_shape: tuple[int, ...]
    full_weight_shape: tuple[int, ...]
    shard_weight_shape: tuple[int, ...]
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


@dataclass(frozen=True)
class KRankBWEmbeddingSequenceReductionCertificate:
    rule_id: str
    rank_count: int
    shard_dim: int
    gradient_fact: RelationFactSpec
    ids_fact: RelationFactSpec
    ids_chunks_fact: RelationFactSpec
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_chunk_steps: tuple[str, ...]
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_embedding_sequence_reduction_frontiers(plan, ir, frontiers, layouts):
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("BW_embedding sequence reduction frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="reduction" or len(frontier)!=5:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_embedding" or sm.side!="sm" or any(x.op!="BW_embedding" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if tuple(int(x.rank) for x in pms)!=(0,1,2,3) or len(sm.input_bindings)!=3 or any(len(x.input_bindings)!=3 for x in pms):
            raise RelationCompositionError("rank-4 BW_embedding sequence writer/input authority mismatch")
        if tuple(sm.input_shapes)!=((1,8,32),(1,8),(8,32)) or tuple(sm.output_shape)!=(8,32):
            raise RelationCompositionError("BW_embedding sequence SM is outside checked theorem shapes")
        if any(tuple(x.input_shapes)!=((1,2,32),(1,2),(8,32)) or tuple(x.output_shape)!=(8,32) for x in pms):
            raise RelationCompositionError("BW_embedding sequence PM is outside checked theorem shapes")
        grefs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        gradient_fact=RelationFactSpec("sharded",grefs,gather_dim=1)
        ids_ref=sm.input_bindings[1];weight_ref=sm.input_bindings[2]
        if not ids_ref.startswith("init:") or not weight_ref.startswith("init:") or any(x.input_bindings[2]!=weight_ref for x in pms):
            raise RelationCompositionError("BW_embedding sequence ids/weight are not shared initial authority")
        chunks=[]
        for rank,step in enumerate(pms):
            chunk=by_id.get(step.input_bindings[1])
            if (chunk is None or chunk.op!="ChunkPrim" or chunk.side!="pm" or int(chunk.rank)!=rank
                    or tuple(chunk.parameters)!=(1,) or tuple(chunk.input_bindings)!=(ids_ref,)
                    or tuple(chunk.output_shape)!=(1,2)):
                raise RelationCompositionError("BW_embedding sequence lacks ordered dim-1 IDs chunks")
            chunks.append(chunk)
        ids_tid=int(ids_ref.split(":",1)[1]);weight_tid=int(weight_ref.split(":",1)[1])
        try:
            ids_fact=init_lineage_relation_fact(ir.init_lineages[ids_tid])
            weight_fact=init_lineage_relation_fact(ir.init_lineages[weight_tid])
        except KeyError as exc:
            raise RelationCompositionError("BW_embedding sequence initial lineage is missing") from exc
        if ids_fact.step_triple!=(ids_ref,ids_ref) or weight_fact.step_triple!=(weight_ref,weight_ref):
            raise RelationCompositionError("BW_embedding sequence initial authority is not singleton")
        ids_chunks_fact = RelationFactSpec(
            "chunked", (ids_ref, *(x.step_id for x in chunks)), gather_dim=1
        )
        output=RelationFactSpec("reduction",tuple(frontier))
        certs.append(KRankBWEmbeddingSequenceReductionCertificate(
            rule_id="bw-embedding-sequence-reduction-rank4",rank_count=4,shard_dim=1,
            gradient_fact=gradient_fact,ids_fact=ids_fact,
            ids_chunks_fact=ids_chunks_fact,weight_fact=weight_fact,
            output_fact=output,sm_step_id=sm.step_id,
            pm_chunk_steps=tuple(x.step_id for x in chunks),pm_step_ids=tuple(x.step_id for x in pms),
            lean_theorem="TrainVerify.Denote.bw_embedding_seqchunk_4shards_1_8_32"))
        rewritten.extend((grefs,ids_fact.step_triple,weight_fact.step_triple))
        rewritten_layouts.extend(("sharded",ids_fact.layout,weight_fact.layout))
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWEmbeddingVocabCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    shard_rows: int
    hidden: int
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    gradient_fact: RelationFactSpec
    ids_fact: RelationFactSpec
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_embedding_vocab_frontiers(
    plan: ProofPlan,
    ir: GoalIR,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankBWEmbeddingVocabCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Pull dim-0 BW_embedding output shards to shared g/ids and weight shards."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("BW_embedding vocab frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 2:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm = by_id[frontier[0]]
            pms = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm.side != "sm" or sm.op != "BW_embedding" or any(
            step.side != "pm" or step.op != "BW_embedding" for step in pms
        ):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        k = len(pms)
        if k <= 0 or int(sm.rank) != 0 or tuple(int(x.rank) for x in pms) != tuple(range(k)):
            raise RelationCompositionError("BW_embedding vocab writers have malformed rank authority")
        if len(sm.input_bindings) != 3 or any(len(x.input_bindings) != 3 for x in pms):
            raise RelationCompositionError("BW_embedding vocab writer arity mismatch")
        full_shape = tuple(sm.output_shape)
        shard_shapes = tuple(tuple(x.output_shape) for x in pms)
        if len(full_shape) != 2 or not shard_shapes or any(x != shard_shapes[0] for x in shard_shapes):
            raise RelationCompositionError("BW_embedding vocab output shapes are malformed")
        shard_shape = shard_shapes[0]
        if len(shard_shape) != 2 or full_shape != (shard_shape[0] * k, shard_shape[1]):
            raise RelationCompositionError("BW_embedding vocab outputs are not exact dim-0 shards")
        shard_rows, hidden = shard_shape
        if shard_rows <= 0 or hidden <= 0:
            raise RelationCompositionError("BW_embedding vocab shard dimensions must be positive")
        expected_offsets = tuple((rank * shard_rows,) for rank in range(k))
        if tuple(tuple(x.parameters) for x in pms) != expected_offsets or tuple(sm.parameters) != ():
            raise RelationCompositionError("BW_embedding vocab offsets are not rank * shardRows")
        sm_g, sm_ids, sm_weight = sm.input_bindings
        pm_g = tuple(x.input_bindings[0] for x in pms)
        pm_ids = tuple(x.input_bindings[1] for x in pms)
        pm_weights = tuple(x.input_bindings[2] for x in pms)
        if len(set(pm_g)) != 1 or len(set(pm_ids)) != 1:
            raise RelationCompositionError("BW_embedding vocab g/ids inputs are not shared PM authority")
        def shared_fact(sm_ref, pm_ref):
            if sm_ref.startswith("init:") and pm_ref.startswith("init:"):
                tid = int(sm_ref.split(":", 1)[1])
                lineage = ir.init_lineages.get(tid)
                if lineage is None:
                    raise RelationCompositionError(
                        f"BW_embedding shared init authority is missing for TID {tid}"
                    )
                authority = init_lineage_relation_fact(lineage)
                if authority.layout not in ("replicated", "joined", "sharded"):
                    raise RelationCompositionError(
                        f"BW_embedding shared init TID {tid} has unsupported layout"
                    )
                if authority.layout == "sharded" and len(lineage.tps) != 1:
                    raise RelationCompositionError(
                        f"BW_embedding shared init TID {tid} is multi-piece sharded"
                    )
                return authority, authority.step_triple, authority.layout
            fact = RelationFactSpec("joined", (sm_ref,), joined_pm_step=pm_ref)
            return fact, (sm_ref, pm_ref), "joined"
        gradient_fact, gradient_frontier, gradient_layout = shared_fact(sm_g, pm_g[0])
        ids_fact, ids_frontier, ids_layout = shared_fact(sm_ids, pm_ids[0])
        weight_fact = RelationFactSpec("sharded", (sm_weight, *pm_weights), gather_dim=0)
        output_fact = RelationFactSpec("sharded", tuple(frontier), gather_dim=0)
        certificates.append(KRankBWEmbeddingVocabCertificate(
            rule_id="bw-embedding-vocab-sharded-k-rank",
            rank_count=k, gather_dim=0, shard_rows=shard_rows, hidden=hidden,
            full_shape=full_shape, shard_shape=shard_shape,
            gradient_fact=gradient_fact, ids_fact=ids_fact, weight_fact=weight_fact,
            output_fact=output_fact, sm_step_id=sm.step_id,
            pm_step_ids=tuple(x.step_id for x in pms),
            lean_theorem="TrainVerify.Denote.bw_embedding_eq_allGather_offset_4shards",
        ))
        rewritten.extend((gradient_frontier, ids_frontier, weight_fact.step_triple))
        rewritten_layouts.extend((gradient_layout, ids_layout, "sharded"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


def advance_k_rank_vocab_sharded_embedding_producer(
    plan: ProofPlan,
    ir: GoalIR,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankVocabShardedEmbeddingProducerCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Decompose exact vocab-offset embedding reductions to InitGoal weight shards."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank vocab embedding frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates: list[KRankVocabShardedEmbeddingProducerCertificate] = []
    rewritten: list[tuple[str, ...]] = []
    rewritten_layouts: list[str] = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "reduction" or len(frontier) < 2:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.side != "sm" or sm_step.op != "FW_embedding" or any(
            step.side != "pm" or step.op != "FW_embedding" for step in pm_steps
        ):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        rank_count = len(pm_steps)
        if int(sm_step.rank) != 0:
            raise RelationCompositionError("K-rank vocab embedding SM writer must have rank zero")
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank vocab embedding PM writers are not exact ordered ranks")
        if len(sm_step.input_bindings) != 2 or any(len(step.input_bindings) != 2 for step in pm_steps):
            raise RelationCompositionError("K-rank vocab embedding input arity mismatch")
        if tuple(getattr(sm_step, "parameters", ())) != ():
            raise RelationCompositionError("K-rank vocab embedding SM must use exact plain embedding semantics")
        ids_refs = (sm_step.input_bindings[0], *(step.input_bindings[0] for step in pm_steps))
        if any(not ref.startswith("init:") for ref in ids_refs) or len(set(ids_refs)) != 1:
            raise RelationCompositionError("K-rank vocab embedding ids authority mismatch")
        try:
            ids_tid = int(ids_refs[0].split(":", 1)[1])
            sm_weight_tid = int(sm_step.input_bindings[1].split(":", 1)[1])
        except (IndexError, ValueError) as exc:
            raise RelationCompositionError("K-rank vocab embedding init authority is malformed") from exc
        lineage = ir.init_lineages.get(sm_weight_tid)
        if lineage is None:
            raise RelationCompositionError("K-rank vocab embedding weight authority is missing")
        expected_weight_refs = (sm_step.input_bindings[1], *(step.input_bindings[1] for step in pm_steps))
        actual_weight_refs = (f"init:{int(lineage.ts)}", *(
            f"init:{int(tid)}" for _rank, tid in lineage.tps
        ))
        if tuple((int(rank), int(tid)) for rank, tid in lineage.tps) != tuple(
            (rank, int(pm_steps[rank].input_bindings[1].split(":", 1)[1]))
            for rank in range(rank_count)
        ) or actual_weight_refs != expected_weight_refs:
            raise RelationCompositionError("K-rank vocab embedding weight authority order mismatch")
        full_weight_shape = tuple(int(value) for value in lineage.tsShape)
        shard_weight_shapes = tuple(tuple(int(value) for value in shape) for shape in lineage.tpShapes)
        if (bool(lineage.replicated) or int(lineage.gatherDim if lineage.gatherDim is not None else 0) != 0
                or len(full_weight_shape) != 2 or len(shard_weight_shapes) != rank_count
                or not shard_weight_shapes or any(shape != shard_weight_shapes[0] for shape in shard_weight_shapes)
                or len(shard_weight_shapes[0]) != 2):
            raise RelationCompositionError("K-rank vocab embedding vocab/hidden shape authority mismatch")
        shard_rows, hidden_size = shard_weight_shapes[0]
        if (shard_rows <= 0 or hidden_size <= 0
                or full_weight_shape != (rank_count * shard_rows, hidden_size)):
            raise RelationCompositionError("K-rank vocab embedding vocab/hidden shape contract fails")
        weight_fact = init_lineage_relation_fact(lineage)
        if weight_fact.layout != "sharded" or weight_fact.gather_dim != 0 or weight_fact.step_triple != expected_weight_refs:
            raise RelationCompositionError("K-rank vocab embedding weight authority order mismatch")
        sm_inputs = tuple(tuple(shape) for shape in getattr(sm_step, "input_shapes", ()))
        pm_inputs = tuple(tuple(tuple(shape) for shape in getattr(step, "input_shapes", ())) for step in pm_steps)
        if len(sm_inputs) != 2 or any(len(shapes) != 2 for shapes in pm_inputs):
            raise RelationCompositionError("K-rank vocab embedding declared input shape arity mismatch")
        ids_shape = sm_inputs[0]
        if (sm_inputs[1] != full_weight_shape
                or any(shapes != (ids_shape, (shard_rows, hidden_size)) for shapes in pm_inputs)):
            raise RelationCompositionError("K-rank vocab embedding vocab/hidden shape declarations disagree")
        output_shape = ids_shape + (hidden_size,)
        if tuple(sm_step.output_shape) != output_shape or any(tuple(step.output_shape) != output_shape for step in pm_steps):
            raise RelationCompositionError("K-rank vocab embedding output vocab/hidden shape contract fails")
        expected_offsets = tuple((rank * shard_rows,) for rank in range(rank_count))
        if tuple(tuple(getattr(step, "parameters", ())) for step in pm_steps) != expected_offsets:
            raise RelationCompositionError("K-rank vocab embedding offset semantics do not match rank * shardRows")
        output_fact = RelationFactSpec("reduction", tuple(frontier))
        spec = get_closed_rule_spec("embedding-vocab-sharded-reduction-k-rank")
        certificates.append(KRankVocabShardedEmbeddingProducerCertificate(
            rule_id=spec.rule_id,
            rank_count=rank_count, ids_tid=ids_tid, shard_rows=shard_rows,
            hidden_size=hidden_size, ids_shape=ids_shape,
            full_weight_shape=full_weight_shape,
            shard_weight_shape=(shard_rows, hidden_size),
            weight_fact=weight_fact, output_fact=output_fact,
            sm_step_id=sm_step.step_id,
            pm_step_ids=tuple(step.step_id for step in pm_steps),
            lean_theorem=spec.lean_theorems[0],
        ))
        rewritten.append(weight_fact.step_triple)
        rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankShardedIdsEmbeddingCertificate:
    rule_id: str
    rank_count: int
    shard_dim: int
    ids_tid: int
    weight_tid: int
    ids_full_shape: tuple[int, ...]
    ids_shard_shape: tuple[int, ...]
    weight_shape: tuple[int, ...]
    output_full_shape: tuple[int, ...]
    output_shard_shape: tuple[int, ...]
    ids_chunks_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_embedding_step: str
    pm_chunk_steps: tuple[str, ...]
    pm_embedding_steps: tuple[str, ...]
    lean_theorem: str


def match_k_rank_sharded_ids_embedding_terminal(
    ir: GoalIR, plan: ProofPlan, *,
    frontier: tuple[str, ...] | None = None,
    expected_gather_dim: int | None = None,
) -> KRankShardedIdsEmbeddingCertificate:
    """Match full IDs against ordered ChunkPrim→embedding rank outputs."""
    target_steps = tuple(plan.target_steps) if frontier is None else tuple(frontier)
    if plan.diagnostics or len(target_steps) < 2:
        raise RelationCompositionError("sharded-ids embedding requires one SM and positive PM targets")
    by_id = _step_map(plan)
    try:
        targets = tuple(by_id[ref] for ref in target_steps)
    except KeyError as exc:
        raise RelationCompositionError("sharded-ids embedding target step is missing") from exc
    sm = targets[0]
    pm = targets[1:]
    k = len(pm)
    if sm.side != "sm" or sm.rank != 0 or sm.op != "FW_embedding":
        raise RelationCompositionError("sharded-ids embedding lacks one plain SM embedding")
    if any(step.side != "pm" or step.op != "FW_embedding" for step in pm):
        raise RelationCompositionError("sharded-ids embedding PM targets are not embeddings")
    if tuple(int(step.rank) for step in pm) != tuple(range(k)):
        raise RelationCompositionError("sharded-ids embedding PM ranks are not ordered")
    if tuple(sm.parameters) or any(tuple(step.parameters) for step in pm):
        raise RelationCompositionError("sharded-ids embedding requires plain embedding semantics")
    if len(sm.input_bindings) != 2 or any(len(step.input_bindings) != 2 for step in pm):
        raise RelationCompositionError("sharded-ids embedding arity mismatch")
    if not sm.input_bindings[0].startswith("init:") or not sm.input_bindings[1].startswith("init:"):
        raise RelationCompositionError("sharded-ids embedding SM inputs are not initial authority")
    ids_tid = int(sm.input_bindings[0].split(":", 1)[1])
    weight_tid = int(sm.input_bindings[1].split(":", 1)[1])
    if any(step.input_bindings[1] != f"init:{weight_tid}" for step in pm):
        raise RelationCompositionError("sharded-ids embedding weight is not shared")
    chunk_steps = []
    for rank, step in enumerate(pm):
        binding = step.input_bindings[0]
        chunk = by_id.get(binding)
        if (chunk is None or chunk.side != "pm" or chunk.op != "ChunkPrim"
                or chunk.rank != rank or len(chunk.input_bindings) != 1
                or chunk.input_bindings[0] != f"init:{ids_tid}"):
            raise RelationCompositionError("sharded-ids embedding lacks ordered IDs chunks")
        chunk_steps.append(chunk)
    shard_dims = {tuple(step.parameters) for step in chunk_steps}
    if len(shard_dims) != 1:
        raise RelationCompositionError("sharded-ids embedding chunk dimensions disagree")
    parameters = next(iter(shard_dims))
    if len(parameters) != 1:
        raise RelationCompositionError("sharded-ids embedding chunk dimension is malformed")
    shard_dim = int(parameters[0])
    ids_full_shape = tuple(int(value) for value in sm.input_shapes[0])
    ids_shard_shapes = tuple(tuple(int(value) for value in step.output_shape) for step in chunk_steps)
    if (not ids_shard_shapes or any(shape != ids_shard_shapes[0] for shape in ids_shard_shapes)
            or shard_dim >= len(ids_full_shape)):
        raise RelationCompositionError("sharded-ids embedding IDs shapes disagree")
    ids_shard_shape = ids_shard_shapes[0]
    if (len(ids_shard_shape) != len(ids_full_shape)
            or any(ids_full_shape[index] != ids_shard_shape[index]
                   for index in range(len(ids_full_shape)) if index != shard_dim)
            or ids_full_shape[shard_dim] != k * ids_shard_shape[shard_dim]):
        raise RelationCompositionError("sharded-ids embedding IDs reconstruction fails")
    weight_shape = tuple(int(value) for value in sm.input_shapes[1])
    if len(weight_shape) != 2 or any(tuple(step.input_shapes[1]) != weight_shape for step in pm):
        raise RelationCompositionError("sharded-ids embedding weight shape mismatch")
    hidden = weight_shape[-1]
    output_full_shape = ids_full_shape + (hidden,)
    output_shard_shape = ids_shard_shape + (hidden,)
    if (tuple(sm.output_shape) != output_full_shape
            or any(tuple(step.output_shape) != output_shard_shape for step in pm)):
        raise RelationCompositionError("sharded-ids embedding output shape mismatch")
    required_dim = plan.relation.gather_dim if expected_gather_dim is None else expected_gather_dim
    if getattr(plan.relation.kind, "value", plan.relation.kind) != "gather" or required_dim != shard_dim:
        raise RelationCompositionError("sharded-ids embedding target relation dimension mismatch")
    ids_chunks_fact = RelationFactSpec(
        "chunked",
        (f"init:{ids_tid}", *(step.step_id for step in chunk_steps)),
        gather_dim=shard_dim,
    )
    output_fact = RelationFactSpec("sharded", target_steps, gather_dim=shard_dim)
    spec = get_closed_rule_spec("embedding-sharded-ids-k-rank")
    return KRankShardedIdsEmbeddingCertificate(
        rule_id=spec.rule_id, rank_count=k,
        shard_dim=shard_dim, ids_tid=ids_tid, weight_tid=weight_tid,
        ids_full_shape=ids_full_shape, ids_shard_shape=ids_shard_shape,
        weight_shape=weight_shape, output_full_shape=output_full_shape,
        output_shard_shape=output_shard_shape,
        ids_chunks_fact=ids_chunks_fact, output_fact=output_fact,
        sm_embedding_step=sm.step_id,
        pm_chunk_steps=tuple(step.step_id for step in chunk_steps),
        pm_embedding_steps=tuple(step.step_id for step in pm),
        lean_theorem=spec.lean_theorems[0],
    )


def advance_k_rank_sharded_ids_embedding_frontiers(
    plan: ProofPlan, ir: GoalIR,
    frontiers: tuple[tuple[str, ...], ...], layouts: tuple[str, ...],
) -> tuple[tuple[KRankShardedIdsEmbeddingCertificate, ...],
           tuple[tuple[str, ...], ...], tuple[str, ...]]:
    """Close exact sequence-sharded embedding frontiers without model cases."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("sharded-ids embedding frontier/layout arity mismatch")
    certificates = []
    remaining = []
    remaining_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded":
            remaining.append(frontier); remaining_layouts.append(layout); continue
        try:
            certificate = match_k_rank_sharded_ids_embedding_terminal(
                ir, plan, frontier=frontier, expected_gather_dim=1,
            )
        except RelationCompositionError:
            remaining.append(frontier); remaining_layouts.append(layout); continue
        certificates.append(certificate)
    return tuple(certificates), tuple(remaining), tuple(remaining_layouts)


@dataclass(frozen=True)
class KRankReductionLinearProducerCertificate:
    rule_id: str
    rank_count: int
    activation_chunk_dim: int
    weight_gather_dim: int
    activation_full_shape: tuple[int, ...]
    activation_shard_shape: tuple[int, ...]
    weight_full_shape: tuple[int, ...]
    weight_shard_shape: tuple[int, ...]
    output_shape: tuple[int, ...]
    activation_fact: RelationFactSpec
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_linear_step: str
    pm_linear_steps: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_reduction_linear_producer_frontiers(
    plan: ProofPlan,
    ir: GoalIR,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankReductionLinearProducerCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Decompose row-parallel FW_linear reductions from exact chunks and InitGoal weights."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank reduction-linear frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates: list[KRankReductionLinearProducerCertificate] = []
    rewritten: list[tuple[str, ...]] = []
    rewritten_layouts: list[str] = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "reduction" or len(frontier) < 2:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        sm_linear = by_id.get(frontier[0])
        pm_linears = tuple(by_id.get(ref) for ref in frontier[1:])
        if sm_linear is None or any(step is None for step in pm_linears):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_linear.side != "sm" or sm_linear.op not in {"FW_linear", "FW_mix_precision_linear"} or any(
            step.side != "pm" or step.op != sm_linear.op for step in pm_linears
        ):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        rank_count = len(pm_linears)
        if int(sm_linear.rank) != 0 or tuple(int(step.rank) for step in pm_linears) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank reduction-linear writers are not exact ordered ranks")
        if tuple(getattr(sm_linear, "parameters", ())) != () or any(
            tuple(getattr(step, "parameters", ())) != () for step in pm_linears
        ):
            raise RelationCompositionError("K-rank reduction-linear writers must declare no parameters")
        if len(sm_linear.input_bindings) != 2 or any(len(step.input_bindings) != 2 for step in pm_linears):
            raise RelationCompositionError("K-rank reduction-linear input arity mismatch")

        sm_activation = by_id.get(sm_linear.input_bindings[0])
        chunks = tuple(by_id.get(step.input_bindings[0]) for step in pm_linears)
        if sm_activation is None or any(chunk is None for chunk in chunks):
            raise RelationCompositionError("K-rank reduction-linear activation lineage is unresolved")
        if sm_activation.side != "sm" or any(chunk.side != "pm" for chunk in chunks):
            raise RelationCompositionError("K-rank reduction-linear activation inputs have incompatible side authority")
        if tuple(int(chunk.rank) for chunk in chunks) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank reduction-linear activation inputs are not ordered ranks")

        activation_full_shape = tuple(sm_activation.output_shape)
        if len(activation_full_shape) not in (2, 3):
            raise RelationCompositionError("K-rank reduction-linear supports exact rank-2/rank-3 activations")
        activation_chunk_dim = len(activation_full_shape) - 1
        if any(
            chunk.op == "ChunkPrim"
            and tuple(getattr(chunk, "parameters", ())) != (activation_chunk_dim,)
            for chunk in chunks
        ):
            raise RelationCompositionError("K-rank reduction-linear activation chunk dimension/orientation mismatch")
        activation_shard_shapes = tuple(tuple(chunk.output_shape) for chunk in chunks)
        if not activation_shard_shapes or any(shape != activation_shard_shapes[0] for shape in activation_shard_shapes[1:]):
            raise RelationCompositionError("K-rank reduction-linear activation shard shapes disagree")
        activation_shard_shape = activation_shard_shapes[0]
        reconstructed_activation = list(activation_shard_shape)
        if activation_chunk_dim >= len(reconstructed_activation):
            raise RelationCompositionError("K-rank reduction-linear activation chunk dimension is invalid")
        reconstructed_activation[activation_chunk_dim] *= rank_count
        if tuple(reconstructed_activation) != activation_full_shape:
            raise RelationCompositionError("K-rank reduction-linear activation chunks do not reconstruct full shape")
        sm_weight_ref = sm_linear.input_bindings[1]
        pm_weight_refs = tuple(step.input_bindings[1] for step in pm_linears)
        try:
            sm_weight_tid = int(sm_weight_ref.split(":", 1)[1])
        except ValueError as exc:
            raise RelationCompositionError("K-rank reduction-linear SM weight TID is invalid") from exc
        lineage = ir.init_lineages.get(sm_weight_tid)
        if lineage is None:
            raise RelationCompositionError("K-rank reduction-linear weight InitGoal is missing")
        weight_full_shape = tuple(int(value) for value in lineage.tsShape)
        if all(ref.startswith("init:") for ref in pm_weight_refs):
            weight_fact = init_lineage_relation_fact(lineage)
            if weight_fact.layout != "sharded" or weight_fact.step_triple != (sm_weight_ref, *pm_weight_refs):
                raise RelationCompositionError("K-rank reduction-linear weight lineage/order mismatch")
            weight_gather_dim = weight_fact.gather_dim
            weight_shard_shapes = tuple(tuple(int(value) for value in shape) for shape in lineage.tpShapes)
        else:
            weight_chunks = tuple(by_id.get(ref) for ref in pm_weight_refs)
            if (any(step is None for step in weight_chunks)
                    or tuple(int(step.rank) for step in weight_chunks) != tuple(range(rank_count))
                    or any(step.op != "ChunkPrim" or tuple(step.parameters) != (1,) for step in weight_chunks)
                    or len({step.input_bindings for step in weight_chunks}) != 1):
                raise RelationCompositionError("K-rank reduction-linear weight shards are not exact dim-1 chunks")
            shared_binding = weight_chunks[0].input_bindings[0]
            seen_aliases = set()
            while not shared_binding.startswith("init:"):
                if shared_binding in seen_aliases or shared_binding not in by_id:
                    raise RelationCompositionError("K-rank reduction-linear weight alias chain is unresolved")
                seen_aliases.add(shared_binding)
                alias = by_id[shared_binding]
                if (alias.op != "FW_multiref" or len(alias.input_bindings) != 1
                        or len(alias.parameters) != 1 or alias.output_index >= alias.parameters[0]):
                    raise RelationCompositionError("K-rank reduction-linear weight source is not a multiref alias")
                shared_binding = alias.input_bindings[0]
            if shared_binding != sm_weight_ref:
                raise RelationCompositionError("K-rank reduction-linear weight chunks do not derive from the SM weight")
            weight_gather_dim = 1
            weight_shard_shapes = tuple(tuple(step.output_shape) for step in weight_chunks)
            weight_fact = RelationFactSpec(
                "chunked", (sm_weight_ref, *pm_weight_refs), gather_dim=weight_gather_dim
            )
        if weight_gather_dim != 1:
            raise RelationCompositionError("K-rank reduction-linear weight gather orientation must be dimension 1")
        if len(weight_full_shape) != 2 or not weight_shard_shapes or any(
            shape != weight_shard_shapes[0] for shape in weight_shard_shapes[1:]
        ):
            raise RelationCompositionError("K-rank reduction-linear weight shapes are not uniform matrices")
        weight_shard_shape = weight_shard_shapes[0]

        declared_sm = tuple(tuple(shape) for shape in sm_linear.input_shapes)
        declared_pm = tuple(tuple(tuple(shape) for shape in step.input_shapes) for step in pm_linears)
        if declared_sm != (activation_full_shape, weight_full_shape):
            raise RelationCompositionError("K-rank reduction-linear SM declared inputs disagree with lineage")
        if declared_pm != tuple((activation_shard_shape, weight_shard_shape) for _ in pm_linears):
            raise RelationCompositionError("K-rank reduction-linear PM declared inputs disagree with lineage")
        inner = activation_full_shape[-1]
        shard = activation_shard_shape[-1]
        if weight_full_shape[1] != inner or weight_shard_shape != (weight_full_shape[0], shard):
            raise RelationCompositionError("K-rank reduction-linear activation/weight contraction orientation mismatch")
        output_shape = tuple(sm_linear.output_shape)
        expected_output = (*activation_full_shape[:-1], weight_full_shape[0])
        if output_shape != expected_output or any(tuple(step.output_shape) != output_shape for step in pm_linears):
            raise RelationCompositionError("K-rank reduction-linear outputs do not have one exact full shape")
        if rank_count <= 0 or shard <= 0 or any(extent <= 0 for extent in activation_full_shape[:-1]) or weight_full_shape[0] <= 0:
            raise RelationCompositionError("K-rank reduction-linear theorem positivity contract fails")

        activation_fact = RelationFactSpec(
            "sharded", (sm_activation.step_id, *(chunk.step_id for chunk in chunks)),
            gather_dim=activation_chunk_dim,
        )
        output_fact = RelationFactSpec("reduction", tuple(frontier))
        theorem = "TrainVerify.Denote.fw_linear_allGather_eq_allReduce_fw_linear_chunk"
        if len(activation_full_shape) == 3:
            theorem += "_3d"
        certificates.append(KRankReductionLinearProducerCertificate(
            rule_id="linear-reduction-producer-k-rank",
            rank_count=rank_count,
            activation_chunk_dim=activation_chunk_dim,
            weight_gather_dim=weight_gather_dim,
            activation_full_shape=activation_full_shape,
            activation_shard_shape=activation_shard_shape,
            weight_full_shape=weight_full_shape,
            weight_shard_shape=weight_shard_shape,
            output_shape=output_shape,
            activation_fact=activation_fact,
            weight_fact=weight_fact,
            output_fact=output_fact,
            sm_linear_step=sm_linear.step_id,
            pm_linear_steps=tuple(step.step_id for step in pm_linears),
            lean_theorem=theorem,
        ))
        rewritten.extend((activation_fact.step_triple, weight_fact.step_triple))
        rewritten_layouts.extend(("sharded", weight_fact.layout))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankHiddenShardedEmbeddingCertificate:
    rule_id: str
    rank_count: int
    ids_tid: int
    ids_shape: tuple[int, ...]
    full_weight_shape: tuple[int, ...]
    shard_weight_shape: tuple[int, ...]
    full_output_shape: tuple[int, ...]
    shard_output_shape: tuple[int, ...]
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_hidden_sharded_embedding(
    plan: ProofPlan,
    ir: GoalIR,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankHiddenShardedEmbeddingCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank embedding frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates: list[KRankHiddenShardedEmbeddingCertificate] = []
    rewritten: list[tuple[str, ...]] = []
    rewritten_layouts: list[str] = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.op != "FW_embedding" or any(step.op != "FW_embedding" for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        k = len(pm_steps)
        if sm_step.side != "sm" or int(sm_step.rank) != 0 or any(step.side != "pm" for step in pm_steps):
            raise RelationCompositionError("K-rank embedding writers have incompatible side/rank authority")
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(k)):
            raise RelationCompositionError("K-rank embedding PM writers are not ordered ranks")
        if tuple(getattr(sm_step, "parameters", ())) != () or any(
            tuple(getattr(step, "parameters", ())) != () for step in pm_steps
        ):
            raise RelationCompositionError("K-rank hidden embedding must use exact plain embedding semantics")
        if len(sm_step.input_bindings) != 2 or any(len(step.input_bindings) != 2 for step in pm_steps):
            raise RelationCompositionError("K-rank embedding input arity mismatch")
        ids_refs = (sm_step.input_bindings[0], *(step.input_bindings[0] for step in pm_steps))
        if any(not ref.startswith("init:") for ref in ids_refs) or len(set(ids_refs)) != 1:
            raise RelationCompositionError("K-rank embedding ids authority mismatch")
        try:
            ids_tid = int(ids_refs[0].split(":", 1)[1])
            sm_weight_tid = int(sm_step.input_bindings[1].split(":", 1)[1])
        except (IndexError, ValueError) as exc:
            raise RelationCompositionError("K-rank embedding init authority is malformed") from exc
        lineage = ir.init_lineages.get(sm_weight_tid)
        if lineage is None:
            raise RelationCompositionError("K-rank embedding weight authority is missing")
        weight_fact = init_lineage_relation_fact(lineage)
        expected_weight_refs = (
            sm_step.input_bindings[1], *(step.input_bindings[1] for step in pm_steps)
        )
        if weight_fact.step_triple != expected_weight_refs or weight_fact.layout != "sharded":
            raise RelationCompositionError("K-rank embedding weight authority order mismatch")
        if weight_fact.gather_dim != 1:
            raise RelationCompositionError("K-rank embedding weight must be hidden-sharded on dimension 1")
        full_weight_shape = tuple(int(value) for value in lineage.tsShape)
        shard_weight_shapes = tuple(tuple(int(value) for value in shape) for shape in lineage.tpShapes)
        declared_sm = tuple(tuple(shape) for shape in sm_step.input_shapes)
        declared_pm = tuple(tuple(tuple(shape) for shape in step.input_shapes) for step in pm_steps)
        if (len(full_weight_shape) != 2 or len(shard_weight_shapes) != k or not shard_weight_shapes
                or any(shape != shard_weight_shapes[0] for shape in shard_weight_shapes[1:])):
            raise RelationCompositionError("K-rank hidden embedding weight shapes are not uniform matrices")
        shard_weight_shape = shard_weight_shapes[0]
        ids_shape = declared_sm[0] if len(declared_sm) == 2 else ()
        if (not ids_shape or declared_sm != (ids_shape, full_weight_shape)
                or declared_pm != tuple((ids_shape, shard_weight_shape) for _ in pm_steps)):
            raise RelationCompositionError("K-rank hidden embedding declared inputs disagree with authority")
        if (full_weight_shape[0] <= 0 or shard_weight_shape[1] <= 0
                or full_weight_shape != (shard_weight_shape[0], k * shard_weight_shape[1])):
            raise RelationCompositionError("K-rank hidden embedding weight reconstruction fails")
        full = tuple(sm_step.output_shape)
        shards = tuple(tuple(step.output_shape) for step in pm_steps)
        if not shards or any(shape != shards[0] for shape in shards[1:]) or len(full) != len(ids_shape) + 1:
            raise RelationCompositionError("K-rank embedding output shard shapes disagree")
        if full != ids_shape + (full_weight_shape[1],) or shards[0] != ids_shape + (shard_weight_shape[1],):
            raise RelationCompositionError("K-rank hidden embedding output shapes disagree with inputs")
        output_rank = len(full)
        hidden_dim = len(ids_shape)
        candidates = [dim for dim in range(output_rank)
                      if full[dim] == shards[0][dim] * k and all(
                          full[index] == shards[0][index]
                          for index in range(output_rank) if index != dim
                      )]
        if candidates != [hidden_dim]:
            raise RelationCompositionError(
                f"K-rank embedding output is not uniquely hidden-sharded: {candidates}"
            )
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=hidden_dim)
        spec = get_closed_rule_spec("embedding-hidden-sharded-k-rank")
        if len(ids_shape) == 1:
            if k != 2:
                raise RelationCompositionError(
                    "vector-ID hidden-sharded embedding currently requires exact two-rank theorem authority"
                )
            lean_theorem = spec.lean_theorems[0]
        elif len(ids_shape) == 2:
            lean_theorem = spec.lean_theorems[1]
        else:
            raise RelationCompositionError(
                "K-rank hidden embedding IDs must have rank one or two"
            )
        certificates.append(KRankHiddenShardedEmbeddingCertificate(
            rule_id=spec.rule_id,
            rank_count=k,
            ids_tid=ids_tid,
            ids_shape=ids_shape,
            full_weight_shape=full_weight_shape,
            shard_weight_shape=shard_weight_shape,
            full_output_shape=full,
            shard_output_shape=shards[0],
            weight_fact=weight_fact,
            output_fact=output_fact,
            sm_step_id=sm_step.step_id,
            pm_step_ids=tuple(step.step_id for step in pm_steps),
            lean_theorem=lean_theorem,
        ))
        rewritten.append(weight_fact.step_triple)
        rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankFullProducerChunksCertificate:
    rule_id: str
    rank_count: int
    chunk_dim: int
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_producer_step: str
    pm_chunk_steps: tuple[str, ...]
    lean_theorem: str


@dataclass(frozen=True)
class KRankAllReduceReconstructionCertificate:
    rule_id: str
    rank_count: int
    full_shape: tuple[int, ...]
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    pm_allreduce_step: str
    lean_theorem: str


@dataclass(frozen=True)
class KRankReduceScatterReconstructionCertificate:
    rule_id: str
    rank_count: int
    scatter_dim: int
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_reduce_scatter_reconstruction_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankReduceScatterReconstructionCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Peel ordered rank-local reduce-scatter writers into a ReductionRel."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("reduce-scatter frontier/layout arity mismatch")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if any(step.op != "ReduceScatterPrim" for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        k = len(pm_steps)
        if (sm_step.side != "sm" or any(step.side != "pm" for step in pm_steps)
                or tuple(step.rank for step in pm_steps) != tuple(range(k))):
            raise RelationCompositionError("reduce-scatter writers lack ordered rank authority")
        if k <= 0 or any(step.parameters != pm_steps[0].parameters for step in pm_steps):
            raise RelationCompositionError("reduce-scatter parameters disagree across ranks")
        if len(pm_steps[0].parameters) != 1:
            raise RelationCompositionError("reduce-scatter lacks one exact shard dimension")
        dim = int(pm_steps[0].parameters[0])
        input_refs = tuple(pm_steps[0].input_bindings)
        if (len(input_refs) != k or any(step.input_bindings != input_refs for step in pm_steps)
                or any(ref.startswith("init:") for ref in input_refs)):
            raise RelationCompositionError("reduce-scatter contribution authority/order mismatch")
        full_shape = tuple(sm_step.output_shape)
        shard_shape = tuple(pm_steps[0].output_shape)
        if (not full_shape or dim >= len(full_shape)
                or any(tuple(shape) != full_shape for step in pm_steps for shape in step.input_shapes)
                or any(tuple(step.output_shape) != shard_shape for step in pm_steps)
                or full_shape[dim] != shard_shape[dim] * k
                or any(full_shape[index] != shard_shape[index]
                       for index in range(len(full_shape)) if index != dim)):
            raise RelationCompositionError("reduce-scatter shapes do not form one exact sharding axis")
        input_fact = RelationFactSpec("reduction", (frontier[0], *input_refs))
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=dim)
        certificates.append(KRankReduceScatterReconstructionCertificate(
            rule_id="reduce-scatter-reconstruction-k-rank",
            rank_count=k, scatter_dim=dim, full_shape=full_shape,
            shard_shape=shard_shape, input_fact=input_fact,
            output_fact=output_fact,
            pm_step_ids=tuple(step.step_id for step in pm_steps),
            lean_theorem="TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn",
        ))
        rewritten.append(input_fact.step_triple)
        rewritten_layouts.append("reduction")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


def advance_k_rank_allreduce_reconstruction_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankAllReduceReconstructionCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Replace a joined rank-0 AllReduce writer by its ordered full-shape inputs."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank AllReduce frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "joined":
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if len(frontier) != 2:
            raise RelationCompositionError("joined K-rank root must contain one SM and one PM ref")
        sm_ref, pm_ref = frontier
        sm_step = by_id.get(sm_ref)
        reduce = by_id.get(pm_ref)
        if sm_step is None or reduce is None:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if sm_step.side != "sm" or reduce.side != "pm":
            raise RelationCompositionError("joined K-rank root has wrong-side writers")
        if reduce.op not in ("AllReducePrim", "CROSS_DP_WRED"):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if int(reduce.rank) != 0:
            raise RelationCompositionError("K-rank AllReduce writer must have rank zero")
        if tuple(reduce.parameters) != ():
            raise RelationCompositionError("K-rank AllReduce writer must declare no parameters")
        input_refs = tuple(reduce.input_bindings)
        rank_count = len(input_refs)
        if rank_count == 0:
            raise RelationCompositionError("K-rank AllReduce must have a nonempty ordered input list")
        input_steps = tuple(by_id.get(ref) for ref in input_refs)
        if any(step is None or step.side != "pm" for step in input_steps):
            raise RelationCompositionError("K-rank AllReduce input writer is unresolved or wrong-side")
        if tuple(int(step.rank) for step in input_steps) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank AllReduce inputs are not in exact rank order")
        contribution_shapes = tuple(tuple(step.output_shape) for step in input_steps)
        full_shape = tuple(sm_step.output_shape)
        if any(shape != full_shape for shape in contribution_shapes):
            raise RelationCompositionError("K-rank AllReduce contributions do not have exact equal full shapes")
        declared_inputs = tuple(tuple(shape) for shape in getattr(reduce, "input_shapes", ()))
        if declared_inputs != contribution_shapes:
            raise RelationCompositionError("K-rank AllReduce declared input shapes disagree with writers")
        if tuple(reduce.output_shape) != full_shape:
            raise RelationCompositionError("K-rank AllReduce output shape disagrees with SM full shape")
        input_fact = RelationFactSpec("reduction", (sm_ref, *input_refs))
        output_fact = RelationFactSpec(
            "joined", (sm_ref,), joined_pm_step=pm_ref
        )
        rule_id = (
            "allreduce-reconstruction-k-rank" if reduce.op == "AllReducePrim"
            else "cross-dp-wred-reconstruction-k-rank"
        )
        spec = CLOSED_RULE_REGISTRY.get(rule_id)
        theorem = (
            spec.lean_theorems[0] if spec is not None
            else "TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce"
        )
        certificates.append(KRankAllReduceReconstructionCertificate(
            rule_id=rule_id,
            rank_count=rank_count,
            full_shape=full_shape,
            input_fact=input_fact,
            output_fact=output_fact,
            pm_allreduce_step=pm_ref,
            lean_theorem=theorem,
        ))
        rewritten.append(input_fact.step_triple)
        rewritten_layouts.append("reduction")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankAllGatherReconstructionCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    pm_allgather_step: str
    lean_theorem: str


def advance_k_rank_allgather_reconstruction_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankAllGatherReconstructionCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Replace a joined PM AllGather root by its ordered sharded input fact."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank AllGather frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "joined":
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if len(frontier) != 2:
            raise RelationCompositionError("joined K-rank root must contain one SM and one PM ref")
        sm_ref, pm_ref = frontier
        sm_step = by_id.get(sm_ref)
        gather = by_id.get(pm_ref)
        if sm_step is None or gather is None:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if sm_step.side != "sm" or gather.side != "pm":
            raise RelationCompositionError("joined K-rank root has wrong-side writers")
        if gather.op != "AllGatherPrim":
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if int(gather.rank) != 0:
            raise RelationCompositionError("K-rank AllGather writer must have rank zero")
        if len(gather.parameters) != 1:
            raise RelationCompositionError("K-rank AllGather must declare exactly one gather dimension")
        gather_dim = int(gather.parameters[0])
        input_refs = tuple(gather.input_bindings)
        rank_count = len(input_refs)
        if rank_count < 2:
            raise RelationCompositionError("K-rank AllGather must have at least two ordered inputs")
        input_steps = tuple(by_id.get(ref) for ref in input_refs)
        if any(step is None or step.side != "pm" for step in input_steps):
            raise RelationCompositionError("K-rank AllGather input writer is unresolved or wrong-side")
        if tuple(int(step.rank) for step in input_steps) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank AllGather inputs are not in exact rank order")
        shard_shapes = tuple(tuple(step.output_shape) for step in input_steps)
        if any(shape != shard_shapes[0] for shape in shard_shapes[1:]):
            raise RelationCompositionError("K-rank AllGather input shard shapes disagree")
        declared_inputs = tuple(tuple(shape) for shape in getattr(gather, "input_shapes", ()))
        if declared_inputs != shard_shapes:
            raise RelationCompositionError("K-rank AllGather declared input shapes disagree with writers")
        shard_shape = shard_shapes[0]
        if gather_dim < 0 or gather_dim >= len(shard_shape):
            raise RelationCompositionError("K-rank AllGather gather dimension is out of bounds")
        full_shape = list(shard_shape)
        full_shape[gather_dim] *= rank_count
        full_shape = tuple(full_shape)
        if tuple(gather.output_shape) != full_shape:
            raise RelationCompositionError("K-rank AllGather declared output shape is not reconstructed")
        if tuple(sm_step.output_shape) != full_shape:
            raise RelationCompositionError("K-rank AllGather output shape disagrees with SM writer")
        input_fact = RelationFactSpec(
            "sharded", (sm_ref, *input_refs), gather_dim=gather_dim
        )
        output_fact = RelationFactSpec(
            "joined", (sm_ref,), joined_pm_step=pm_ref
        )
        spec = get_closed_rule_spec("allgather-reconstruction-k-rank")
        certificates.append(KRankAllGatherReconstructionCertificate(
            rule_id=spec.rule_id,
            rank_count=rank_count,
            gather_dim=gather_dim,
            full_shape=full_shape,
            shard_shape=shard_shape,
            input_fact=input_fact,
            output_fact=output_fact,
            pm_allgather_step=pm_ref,
            lean_theorem=spec.lean_theorems[0],
        ))
        rewritten.append(input_fact.step_triple)
        rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


def advance_k_rank_full_producer_chunks(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankFullProducerChunksCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank full-producer frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates: list[KRankFullProducerChunksCertificate] = []
    rewritten: list[tuple[str, ...]] = []
    rewritten_layouts: list[str] = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            chunks = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if any(step.side != "pm" or step.op != "ChunkPrim" for step in chunks):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        k = len(chunks)
        if tuple(int(step.rank) for step in chunks) != tuple(range(k)):
            raise RelationCompositionError("K-rank full-producer chunks are not ordered ranks")
        if any(len(step.input_bindings) != 1 for step in chunks):
            raise RelationCompositionError("K-rank full-producer chunk input arity mismatch")
        producer_refs = tuple(step.input_bindings[0] for step in chunks)
        if len(set(producer_refs)) != 1:
            raise RelationCompositionError("K-rank chunks do not share one full producer")
        try:
            producer = by_id[producer_refs[0]]
        except KeyError as exc:
            raise RelationCompositionError("K-rank full producer is unresolved") from exc
        if producer.side != "pm":
            raise RelationCompositionError("K-rank full producer is not a PM step")
        if tuple(sm_step.output_shape) != tuple(producer.output_shape):
            raise RelationCompositionError("K-rank full producer shape differs from SM output")
        parameter_sets = tuple(tuple(step.parameters) for step in chunks)
        if any(len(params) != 1 for params in parameter_sets) or len(set(parameter_sets)) != 1:
            raise RelationCompositionError("K-rank chunks do not share one literal chunk dimension")
        chunk_dim = int(parameter_sets[0][0])
        full_shape = tuple(sm_step.output_shape)
        shard_shapes = tuple(tuple(step.output_shape) for step in chunks)
        if not shard_shapes or any(shape != shard_shapes[0] for shape in shard_shapes[1:]):
            raise RelationCompositionError("K-rank chunk output shapes disagree")
        if chunk_dim < 0 or chunk_dim >= len(full_shape):
            raise RelationCompositionError("K-rank chunk dimension is invalid")
        reconstructed = list(shard_shapes[0])
        reconstructed[chunk_dim] *= k
        if tuple(reconstructed) != full_shape:
            raise RelationCompositionError("K-rank chunk reconstruction shape contract fails")
        input_fact = RelationFactSpec(
            "joined", (sm_step.step_id,), joined_pm_step=producer.step_id
        )
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=chunk_dim)
        spec = get_closed_rule_spec("full-producer-chunks-k-rank")
        certificates.append(KRankFullProducerChunksCertificate(
            rule_id=spec.rule_id,
            rank_count=k,
            chunk_dim=chunk_dim,
            input_fact=input_fact,
            output_fact=output_fact,
            sm_step_id=sm_step.step_id,
            pm_producer_step=producer.step_id,
            pm_chunk_steps=tuple(step.step_id for step in chunks),
            lean_theorem=spec.lean_theorems[0],
        ))
        rewritten.append((sm_step.step_id, producer.step_id))
        rewritten_layouts.append("joined")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankOutputShardedLinearCertificate:
    rule_id: str
    rank_count: int
    output_gather_dim: int
    activation_fact: RelationFactSpec
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    activation_shape: tuple[int, ...]
    weight_full_shape: tuple[int, ...]
    weight_shard_shape: tuple[int, ...]
    output_full_shape: tuple[int, ...]
    output_shard_shape: tuple[int, ...]
    lean_theorem: str


def advance_k_rank_output_sharded_linear_frontiers(
    plan: ProofPlan,
    ir: GoalIR,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankOutputShardedLinearCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank output-linear frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates: list[KRankOutputShardedLinearCertificate] = []
    rewritten: list[tuple[str, ...]] = []
    rewritten_layouts: list[str] = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.op not in {"FW_linear", "FW_mix_precision_linear"} or any(
            step.op != sm_step.op for step in pm_steps
        ):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        k = len(pm_steps)
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(k)):
            raise RelationCompositionError("K-rank output-linear PM writers are not ordered ranks")
        if len(sm_step.input_bindings) != 2 or any(len(step.input_bindings) != 2 for step in pm_steps):
            raise RelationCompositionError("K-rank output-linear input arity mismatch")
        activation_refs = tuple(step.input_bindings[0] for step in pm_steps)
        if len(set(activation_refs)) != 1:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        sm_weight_ref = sm_step.input_bindings[1]
        pm_weight_refs = tuple(step.input_bindings[1] for step in pm_steps)
        if not sm_weight_ref.startswith("init:"):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_weight_tid = int(sm_weight_ref.split(":", 1)[1])
        except ValueError as exc:
            raise RelationCompositionError("invalid output-linear weight authority") from exc
        lineage = ir.init_lineages.get(sm_weight_tid)
        if lineage is None:
            raise RelationCompositionError("missing output-linear weight authority")
        if all(ref.startswith("init:") for ref in pm_weight_refs):
            weight_fact = init_lineage_relation_fact(lineage)
            expected_weight_refs = (sm_weight_ref, *pm_weight_refs)
            if weight_fact.layout != "sharded" or weight_fact.step_triple != expected_weight_refs:
                raise RelationCompositionError("output-linear weight authority order mismatch")
        else:
            weight_chunks = tuple(by_id.get(ref) for ref in pm_weight_refs)
            if (any(step is None for step in weight_chunks)
                    or tuple(int(step.rank) for step in weight_chunks) != tuple(range(k))
                    or any(step.op != "ChunkPrim" or tuple(step.parameters) != (0,)
                           for step in weight_chunks)
                    or len({step.input_bindings for step in weight_chunks}) != 1):
                rewritten.append(frontier); rewritten_layouts.append(layout); continue
            shared_binding = weight_chunks[0].input_bindings[0]
            seen_aliases = set()
            while not shared_binding.startswith("init:"):
                if shared_binding in seen_aliases or shared_binding not in by_id:
                    raise RelationCompositionError("output-linear weight alias chain is unresolved")
                seen_aliases.add(shared_binding)
                alias = by_id[shared_binding]
                if (alias.op != "FW_multiref" or len(alias.input_bindings) != 1
                        or len(alias.parameters) != 1
                        or not 0 <= alias.output_index < alias.parameters[0]):
                    raise RelationCompositionError("output-linear weight source is not a multiref alias")
                shared_binding = alias.input_bindings[0]
            if shared_binding != sm_weight_ref:
                raise RelationCompositionError("output-linear weight chunks do not derive from the SM weight")
            weight_fact = RelationFactSpec(
                "chunked", (sm_weight_ref, *pm_weight_refs), gather_dim=0
            )
        if weight_fact.gather_dim != 0:
            raise RelationCompositionError("output-linear weight authority must gather dimension 0")
        sm_activation_ref = sm_step.input_bindings[0]
        pm_activation_ref = activation_refs[0]
        try:
            sm_activation = by_id[sm_activation_ref]
            pm_activation = by_id[pm_activation_ref]
        except KeyError as exc:
            raise RelationCompositionError("output-linear activation producer is unresolved") from exc
        if tuple(sm_activation.output_shape) != tuple(pm_activation.output_shape):
            raise RelationCompositionError("output-linear activation shapes disagree")
        full = tuple(sm_step.output_shape)
        shards = tuple(tuple(step.output_shape) for step in pm_steps)
        tensor_rank = len(full)
        if (not shards or any(shape != shards[0] for shape in shards[1:])
                or tensor_rank not in {2, 3}):
            raise RelationCompositionError("output-linear shard shapes disagree")
        candidates = [dim for dim in range(tensor_rank) if full[dim] == shards[0][dim] * k and all(
            full[index] == shards[0][index] for index in range(tensor_rank) if index != dim
        )]
        if len(candidates) != 1:
            raise RelationCompositionError(
                f"output-linear does not determine one gather dimension: {candidates}"
            )
        output_dim = candidates[0]
        activation_fact = RelationFactSpec(
            "joined", (sm_activation_ref,), joined_pm_step=pm_activation_ref
        )
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=output_dim)
        activation_shape = tuple(sm_activation.output_shape)
        weight_full_shape = tuple(lineage.tsShape)
        weight_shard_shape = tuple(pm_steps[0].input_shapes[1])
        if any(tuple(step.input_shapes[1]) != weight_shard_shape for step in pm_steps):
            raise RelationCompositionError("output-linear weight shard shapes disagree")
        if tensor_rank == 2:
            if (k != 2 or output_dim != 1 or len(activation_shape) != 2
                    or weight_full_shape != (weight_shard_shape[0] * 2, weight_shard_shape[1])
                    or activation_shape[1] != weight_full_shape[1]
                    or min((*activation_shape, *weight_shard_shape)) <= 0):
                raise RelationCompositionError("rank-2 output-linear theorem contract fails")
            rule_id = "linear-output-sharded-two-rank-2d"
            lean_theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_linear_output_dim1_two_2d"
        else:
            spec = get_closed_rule_spec("linear-output-sharded-k-rank")
            rule_id = spec.rule_id
            lean_theorem = spec.lean_theorems[0]
        certificates.append(KRankOutputShardedLinearCertificate(
            rule_id=rule_id,
            rank_count=k,
            output_gather_dim=output_dim,
            activation_fact=activation_fact,
            weight_fact=weight_fact,
            output_fact=output_fact,
            sm_step_id=sm_step.step_id,
            pm_step_ids=tuple(step.step_id for step in pm_steps),
            activation_shape=activation_shape,
            weight_full_shape=weight_full_shape,
            weight_shard_shape=weight_shard_shape,
            output_full_shape=full,
            output_shard_shape=shards[0],
            lean_theorem=lean_theorem,
        ))
        rewritten.extend(((sm_activation_ref, pm_activation_ref), weight_fact.step_triple))
        rewritten_layouts.extend(("joined", weight_fact.layout))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankMatmulOutputAxisCertificate:
    rule_id: str
    rank_count: int
    output_gather_dim: int
    first_operand_fact: RelationFactSpec
    second_operand_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    first_operand_shape: tuple[int, ...]
    second_operand_full_shape: tuple[int, ...]
    second_operand_shard_shape: tuple[int, ...]
    output_full_shape: tuple[int, ...]
    output_shard_shape: tuple[int, ...]
    lean_theorem: str


def advance_k_rank_matmul_output_axis_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[KRankMatmulOutputAxisCertificate, ...], tuple[tuple[str, ...], ...], tuple[str, ...]]:
    """Pull dim-3 rank-4 matmul outputs to joined-X and dim-3-sharded-Y facts."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank matmul frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.op != "FW_matmul" or any(step.op != "FW_matmul" for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        rank_count = len(pm_steps)
        if sm_step.side != "sm" or int(sm_step.rank) != 0 or any(step.side != "pm" for step in pm_steps):
            raise RelationCompositionError("K-rank matmul writers have incompatible side/rank authority")
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank matmul PM writers are not exact ordered ranks")
        writers = (sm_step, *pm_steps)
        if any(tuple(step.parameters) for step in writers):
            raise RelationCompositionError("K-rank FW_matmul writers must declare no parameters")
        if any(len(step.input_bindings) != 2 for step in writers):
            raise RelationCompositionError("K-rank FW_matmul writer input arity mismatch")
        if any(len(step.input_shapes) != 2 for step in writers):
            raise RelationCompositionError("K-rank FW_matmul declared input shapes are missing")
        sm_x_ref, sm_y_ref = sm_step.input_bindings
        pm_x_refs = tuple(step.input_bindings[0] for step in pm_steps)
        pm_y_refs = tuple(step.input_bindings[1] for step in pm_steps)
        shared_first_operand = len(set(pm_x_refs)) == 1
        # Classify family A by shared-X authority plus dim-3 output layout.
        # Rank-local X belongs to the distinct head/query-sharded families and
        # remains unresolved here. Once X is shared, malformed dim-3 output
        # authority is a genuine family-A error and fails closed.
        if not shared_first_operand:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        out_full_shape = tuple(sm_step.output_shape)
        out_shard_shapes = tuple(tuple(step.output_shape) for step in pm_steps)
        if (len(out_full_shape) != 4 or not out_shard_shapes
                or any(shape != out_shard_shapes[0] for shape in out_shard_shapes)):
            raise RelationCompositionError("K-rank matmul outputs must have exact equal rank-4 shard shapes")
        out_shard_shape = out_shard_shapes[0]
        expected_output_full = list(out_shard_shape)
        expected_output_full[3] *= rank_count
        if tuple(expected_output_full) != out_full_shape:
            raise RelationCompositionError("K-rank matmul output is not an exact dim3 sharding")
        try:
            sm_x, pm_x, sm_y = by_id[sm_x_ref], by_id[pm_x_refs[0]], by_id[sm_y_ref]
            pm_ys = tuple(by_id[ref] for ref in pm_y_refs)
        except KeyError as exc:
            raise RelationCompositionError("K-rank matmul input authority is unresolved") from exc
        if sm_x.side != "sm" or pm_x.side != "pm":
            raise RelationCompositionError("K-rank matmul first operand lacks joined SM/PM authority")
        if sm_y.side != "sm" or any(step.side != "pm" for step in pm_ys):
            raise RelationCompositionError("K-rank matmul second operand has wrong-side authority")
        if tuple(int(step.rank) for step in pm_ys) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank matmul second-operand shards are not exact ordered ranks")
        x_shape, pm_x_shape = tuple(sm_x.output_shape), tuple(pm_x.output_shape)
        y_full_shape = tuple(sm_y.output_shape)
        y_shard_shapes = tuple(tuple(step.output_shape) for step in pm_ys)
        out_full_shape = tuple(sm_step.output_shape)
        out_shard_shapes = tuple(tuple(step.output_shape) for step in pm_steps)
        if len(x_shape) != 4 or pm_x_shape != x_shape:
            raise RelationCompositionError("K-rank matmul first operand must have one exact joined rank-4 shape")
        if len(y_full_shape) != 4 or not y_shard_shapes or any(shape != y_shard_shapes[0] for shape in y_shard_shapes):
            raise RelationCompositionError("K-rank matmul second operand must have exact equal rank-4 shard shapes")
        y_shard_shape = y_shard_shapes[0]
        expected = list(y_shard_shape); expected[3] *= rank_count
        if tuple(expected) != y_full_shape:
            raise RelationCompositionError("K-rank matmul second operand is not an exact dim3 sharding")
        if len(out_full_shape) != 4 or not out_shard_shapes or any(shape != out_shard_shapes[0] for shape in out_shard_shapes):
            raise RelationCompositionError("K-rank matmul outputs must have exact equal rank-4 shard shapes")
        out_shard_shape = out_shard_shapes[0]
        expected = list(out_shard_shape); expected[3] *= rank_count
        if tuple(expected) != out_full_shape:
            raise RelationCompositionError("K-rank matmul output is not an exact dim3 sharding")
        b, h, q, inner = x_shape
        if (y_full_shape != (b, h, inner, out_full_shape[3])
                or y_shard_shape != (b, h, inner, out_shard_shape[3])
                or out_full_shape != (b, h, q, out_full_shape[3])
                or out_shard_shape != (b, h, q, out_shard_shape[3])):
            raise RelationCompositionError("K-rank matmul rank-4 dimensions do not compose")
        declared_sm = tuple(tuple(shape) for shape in sm_step.input_shapes)
        declared_pm = tuple(tuple(tuple(shape) for shape in step.input_shapes) for step in pm_steps)
        if declared_sm != (x_shape, y_full_shape) or declared_pm != tuple((x_shape, y_shard_shape) for _ in range(rank_count)):
            raise RelationCompositionError("K-rank matmul declared input shapes disagree with authority")
        first_fact = RelationFactSpec(
            "joined", (sm_x_ref,), joined_pm_step=pm_x_refs[0]
        )
        second_fact = RelationFactSpec("sharded", (sm_y_ref, *pm_y_refs), gather_dim=3)
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=3)
        spec = get_closed_rule_spec("matmul-output-axis-sharded-k-rank-dim3")
        certificates.append(KRankMatmulOutputAxisCertificate(
            spec.rule_id, rank_count, 3, first_fact,
            second_fact, output_fact, sm_step.step_id, tuple(step.step_id for step in pm_steps),
            x_shape, y_full_shape, y_shard_shape, out_full_shape, out_shard_shape,
            spec.lean_theorems[0],
        ))
        rewritten.extend(((sm_x_ref, pm_x_refs[0]), second_fact.step_triple))
        rewritten_layouts.extend(("joined", "sharded"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankMatmulHeadAxisCertificate:
    rule_id: str
    rank_count: int
    output_gather_dim: int
    first_operand_fact: RelationFactSpec
    second_operand_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    first_operand_full_shape: tuple[int, ...]
    first_operand_shard_shape: tuple[int, ...]
    second_operand_full_shape: tuple[int, ...]
    second_operand_shard_shape: tuple[int, ...]
    output_full_shape: tuple[int, ...]
    output_shard_shape: tuple[int, ...]
    lean_theorem: str


def advance_k_rank_matmul_head_axis_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[KRankMatmulHeadAxisCertificate, ...], tuple[tuple[str, ...], ...], tuple[str, ...]]:
    """Pull aligned dim-1 rank-4 matmuls to two ordered dim-1 shard facts."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank head-axis matmul frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.op != "FW_matmul" or any(step.op != "FW_matmul" for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        rank_count = len(pm_steps)
        if sm_step.side != "sm" or int(sm_step.rank) != 0 or any(step.side != "pm" for step in pm_steps):
            raise RelationCompositionError("K-rank head-axis matmul writers have incompatible side/rank authority")
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank head-axis matmul PM writers are not exact ordered ranks")
        writers = (sm_step, *pm_steps)
        if any(tuple(step.parameters) for step in writers):
            raise RelationCompositionError("K-rank head-axis FW_matmul writers must declare no parameters")
        if any(len(step.input_bindings) != 2 for step in writers):
            raise RelationCompositionError("K-rank head-axis FW_matmul writer input arity mismatch")
        if any(len(step.input_shapes) != 2 for step in writers):
            raise RelationCompositionError("K-rank head-axis FW_matmul declared input shapes are missing")
        sm_x_ref, sm_y_ref = sm_step.input_bindings
        pm_x_refs = tuple(step.input_bindings[0] for step in pm_steps)
        pm_y_refs = tuple(step.input_bindings[1] for step in pm_steps)
        # Shared operands belong to the output/query-axis families. This family
        # requires rank-local authority on both sides and preserves zip pairing.
        x_authority_count, y_authority_count = len(set(pm_x_refs)), len(set(pm_y_refs))
        if x_authority_count == 1 or y_authority_count == 1:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if x_authority_count != rank_count:
            raise RelationCompositionError("K-rank head-axis first-operand shards do not preserve rank-wise ordered ranks")
        if y_authority_count != rank_count:
            raise RelationCompositionError("K-rank head-axis second-operand shards do not preserve rank-wise ordered ranks")
        try:
            sm_x, sm_y = by_id[sm_x_ref], by_id[sm_y_ref]
            pm_xs = tuple(by_id[ref] for ref in pm_x_refs)
            pm_ys = tuple(by_id[ref] for ref in pm_y_refs)
        except KeyError as exc:
            raise RelationCompositionError("K-rank head-axis matmul input authority is unresolved") from exc
        if sm_x.side != "sm" or sm_y.side != "sm" or any(step.side != "pm" for step in (*pm_xs, *pm_ys)):
            raise RelationCompositionError("K-rank head-axis matmul input authority has wrong sides")
        expected_ranks = tuple(range(rank_count))
        if tuple(int(step.rank) for step in pm_xs) != expected_ranks:
            raise RelationCompositionError("K-rank head-axis first-operand shards are not exact ordered ranks")
        if tuple(int(step.rank) for step in pm_ys) != expected_ranks:
            raise RelationCompositionError("K-rank head-axis second-operand shards are not exact ordered ranks")
        x_full, y_full, out_full = tuple(sm_x.output_shape), tuple(sm_y.output_shape), tuple(sm_step.output_shape)
        x_shards = tuple(tuple(step.output_shape) for step in pm_xs)
        y_shards = tuple(tuple(step.output_shape) for step in pm_ys)
        out_shards = tuple(tuple(step.output_shape) for step in pm_steps)
        all_shapes = (x_full, y_full, out_full, *x_shards, *y_shards, *out_shards)
        if any(len(shape) != 4 for shape in all_shapes):
            raise RelationCompositionError("K-rank head-axis matmul requires exact rank-4 shapes")
        if (any(shape != x_shards[0] for shape in x_shards[1:])
                or any(shape != y_shards[0] for shape in y_shards[1:])
                or any(shape != out_shards[0] for shape in out_shards[1:])):
            raise RelationCompositionError("K-rank head-axis matmul shard shapes disagree")
        x_shard, y_shard, out_shard = x_shards[0], y_shards[0], out_shards[0]
        b, local_h, q, inner = x_shard
        m = y_shard[3]
        if (local_h <= 0 or q <= 0 or inner <= 0 or m <= 0
                or x_full != (b, local_h * rank_count, q, inner)
                or y_full != (b, local_h * rank_count, inner, m)
                or y_shard != (b, local_h, inner, m)
                or out_full != (b, local_h * rank_count, q, m)
                or out_shard != (b, local_h, q, m)):
            raise RelationCompositionError("K-rank head-axis matmul exact symbolic rank-4 shapes do not compose")
        declared_sm = tuple(tuple(shape) for shape in sm_step.input_shapes)
        declared_pm = tuple(tuple(tuple(shape) for shape in step.input_shapes) for step in pm_steps)
        if declared_sm != (x_full, y_full) or declared_pm != tuple((x_shard, y_shard) for _ in range(rank_count)):
            raise RelationCompositionError("K-rank head-axis matmul declared input shapes disagree with authority")
        first_fact = RelationFactSpec("sharded", (sm_x_ref, *pm_x_refs), gather_dim=1)
        second_fact = RelationFactSpec("sharded", (sm_y_ref, *pm_y_refs), gather_dim=1)
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=1)
        spec = get_closed_rule_spec("matmul-head-axis-sharded-k-rank-dim1")
        certificates.append(KRankMatmulHeadAxisCertificate(
            spec.rule_id, rank_count, 1,
            first_fact, second_fact, output_fact, sm_step.step_id,
            tuple(step.step_id for step in pm_steps), x_full, x_shard,
            y_full, y_shard, out_full, out_shard,
            spec.lean_theorems[0],
        ))
        rewritten.extend((first_fact.step_triple, second_fact.step_triple))
        rewritten_layouts.extend(("sharded", "sharded"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankMatmulQueryAxisCertificate:
    rule_id: str
    rank_count: int
    output_gather_dim: int
    first_operand_fact: RelationFactSpec
    second_operand_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    first_operand_full_shape: tuple[int, ...]
    first_operand_shard_shape: tuple[int, ...]
    second_operand_shape: tuple[int, ...]
    output_full_shape: tuple[int, ...]
    output_shard_shape: tuple[int, ...]
    lean_theorem: str


def advance_k_rank_matmul_query_axis_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[KRankMatmulQueryAxisCertificate, ...], tuple[tuple[str, ...], ...], tuple[str, ...]]:
    """Pull dim-2 rank-4 matmul outputs to dim-2-sharded X and joined/shared Y."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank query-axis matmul frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.op != "FW_matmul" or any(step.op != "FW_matmul" for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        rank_count = len(pm_steps)
        if sm_step.side != "sm" or int(sm_step.rank) != 0 or any(step.side != "pm" for step in pm_steps):
            raise RelationCompositionError("K-rank query-axis matmul writers have incompatible side/rank authority")
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank query-axis matmul PM writers are not exact ordered ranks")
        writers = (sm_step, *pm_steps)
        if any(tuple(step.parameters) for step in writers):
            raise RelationCompositionError("K-rank query-axis FW_matmul writers must declare no parameters")
        if any(len(step.input_bindings) != 2 for step in writers):
            raise RelationCompositionError("K-rank query-axis FW_matmul writer input arity mismatch")
        if any(len(step.input_shapes) != 2 for step in writers):
            raise RelationCompositionError("K-rank query-axis FW_matmul declared input shapes are missing")
        sm_x_ref, sm_y_ref = sm_step.input_bindings
        pm_x_refs = tuple(step.input_bindings[0] for step in pm_steps)
        pm_y_refs = tuple(step.input_bindings[1] for step in pm_steps)
        if len(set(pm_y_refs)) != 1:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        out_full_shape = tuple(sm_step.output_shape)
        out_shard_shapes = tuple(tuple(step.output_shape) for step in pm_steps)
        if (len(out_full_shape) != 4 or not out_shard_shapes
                or any(len(shape) != 4 or shape != out_shard_shapes[0] for shape in out_shard_shapes)):
            raise RelationCompositionError("K-rank query-axis matmul outputs must have exact equal rank-4 shard shapes")
        out_shard_shape = out_shard_shapes[0]
        expected_out = list(out_shard_shape); expected_out[2] *= rank_count
        if tuple(expected_out) != out_full_shape:
            raise RelationCompositionError("K-rank query-axis matmul output is not an exact dim2 sharding")
        try:
            sm_x = by_id[sm_x_ref]
            pm_xs = tuple(by_id[ref] for ref in pm_x_refs)
            sm_y, pm_y = by_id[sm_y_ref], by_id[pm_y_refs[0]]
        except KeyError as exc:
            raise RelationCompositionError("K-rank query-axis matmul input authority is unresolved") from exc
        if sm_x.side != "sm" or any(step.side != "pm" for step in pm_xs):
            raise RelationCompositionError("K-rank query-axis matmul first operand has wrong-side authority")
        if tuple(int(step.rank) for step in pm_xs) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank query-axis matmul first-operand shards are not exact ordered ranks")
        if sm_y.side != "sm" or pm_y.side != "pm":
            raise RelationCompositionError("K-rank query-axis matmul second operand lacks joined SM/PM authority")
        x_full_shape = tuple(sm_x.output_shape)
        x_shard_shapes = tuple(tuple(step.output_shape) for step in pm_xs)
        y_shape, pm_y_shape = tuple(sm_y.output_shape), tuple(pm_y.output_shape)
        if (len(x_full_shape) != 4 or not x_shard_shapes
                or any(len(shape) != 4 or shape != x_shard_shapes[0] for shape in x_shard_shapes)):
            raise RelationCompositionError("K-rank query-axis matmul first operand requires exact rank-4 shards")
        x_shard_shape = x_shard_shapes[0]
        expected_x = list(x_shard_shape); expected_x[2] *= rank_count
        if tuple(expected_x) != x_full_shape:
            raise RelationCompositionError("K-rank query-axis matmul first operand is not an exact dim2 sharding")
        if len(y_shape) != 4 or pm_y_shape != y_shape:
            raise RelationCompositionError("K-rank query-axis matmul second operand requires exact joined rank-4 shape")
        b, h, local_q, inner = x_shard_shape
        m = y_shape[3]
        if (x_full_shape != (b, h, local_q * rank_count, inner)
                or y_shape != (b, h, inner, m)
                or out_full_shape != (b, h, local_q * rank_count, m)
                or out_shard_shape != (b, h, local_q, m)):
            raise RelationCompositionError("K-rank query-axis matmul rank-4 dimensions do not compose")
        declared_sm = tuple(tuple(shape) for shape in sm_step.input_shapes)
        declared_pm = tuple(tuple(tuple(shape) for shape in step.input_shapes) for step in pm_steps)
        if (declared_sm != (x_full_shape, y_shape)
                or declared_pm != tuple((x_shard_shape, y_shape) for _ in range(rank_count))):
            raise RelationCompositionError("K-rank query-axis matmul declared input shapes disagree with authority")
        first_fact = RelationFactSpec("sharded", (sm_x_ref, *pm_x_refs), gather_dim=2)
        second_fact = RelationFactSpec(
            "joined", (sm_y_ref,), joined_pm_step=pm_y_refs[0]
        )
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=2)
        spec = get_closed_rule_spec("matmul-query-axis-sharded-k-rank-dim2")
        certificates.append(KRankMatmulQueryAxisCertificate(
            spec.rule_id, rank_count, 2,
            first_fact, second_fact, output_fact, sm_step.step_id,
            tuple(step.step_id for step in pm_steps), x_full_shape, x_shard_shape,
            y_shape, out_full_shape, out_shard_shape,
            spec.lean_theorems[0],
        ))
        rewritten.extend((first_fact.step_triple, (sm_y_ref, pm_y_refs[0])))
        rewritten_layouts.extend(("sharded", "joined"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankMatmulContractionCertificate:
    rule_id: str
    rank_count: int
    first_operand_fact: RelationFactSpec
    second_operand_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    first_operand_full_shape: tuple[int, ...]
    first_operand_shard_shape: tuple[int, ...]
    second_operand_full_shape: tuple[int, ...]
    second_operand_shard_shape: tuple[int, ...]
    output_shape: tuple[int, ...]
    lean_theorem: str


def advance_k_rank_matmul_contraction_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[KRankMatmulContractionCertificate, ...], tuple[tuple[str, ...], ...], tuple[str, ...]]:
    """Pull rank-wise contraction matmuls to dim-3/dim-2 ShardedRel inputs."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank contraction frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "reduction" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.op != "FW_matmul" or any(step.op != "FW_matmul" for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        k = len(pm_steps)
        if sm_step.side != "sm" or int(sm_step.rank) != 0 or any(step.side != "pm" for step in pm_steps):
            raise RelationCompositionError("K-rank contraction writers have incompatible side/rank authority")
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(k)):
            raise RelationCompositionError("K-rank contraction PM writers are not exact ordered ranks")
        writers = (sm_step, *pm_steps)
        if any(tuple(step.parameters) for step in writers):
            raise RelationCompositionError("K-rank FW_matmul contraction writers must declare no parameters")
        if any(len(step.input_bindings) != 2 for step in writers):
            raise RelationCompositionError("K-rank FW_matmul contraction writer input arity mismatch")
        if any(len(step.input_shapes) != 2 for step in writers):
            raise RelationCompositionError("K-rank FW_matmul contraction declared input shapes are missing")
        sm_x_ref, sm_y_ref = sm_step.input_bindings
        pm_x_refs = tuple(step.input_bindings[0] for step in pm_steps)
        pm_y_refs = tuple(step.input_bindings[1] for step in pm_steps)
        try:
            sm_x, sm_y = by_id[sm_x_ref], by_id[sm_y_ref]
            pm_xs = tuple(by_id[ref] for ref in pm_x_refs)
            pm_ys = tuple(by_id[ref] for ref in pm_y_refs)
        except KeyError as exc:
            raise RelationCompositionError("K-rank contraction input authority is unresolved") from exc
        if sm_x.side != "sm" or sm_y.side != "sm" or any(step.side != "pm" for step in (*pm_xs, *pm_ys)):
            raise RelationCompositionError("K-rank contraction inputs have wrong-side authority")
        expected_ranks = tuple(range(k))
        if (tuple(int(step.rank) for step in pm_xs) != expected_ranks
                or tuple(int(step.rank) for step in pm_ys) != expected_ranks):
            raise RelationCompositionError("K-rank contraction inputs do not preserve exact rank-wise zip pairing")
        x_full = tuple(sm_x.output_shape)
        x_shards = tuple(tuple(step.output_shape) for step in pm_xs)
        y_full = tuple(sm_y.output_shape)
        y_shards = tuple(tuple(step.output_shape) for step in pm_ys)
        output = tuple(sm_step.output_shape)
        pm_outputs = tuple(tuple(step.output_shape) for step in pm_steps)
        if len(x_full) != 4 or not x_shards or any(shape != x_shards[0] for shape in x_shards):
            raise RelationCompositionError("K-rank contraction first operand requires exact equal rank-4 shards")
        if len(y_full) != 4 or not y_shards or any(shape != y_shards[0] for shape in y_shards):
            raise RelationCompositionError("K-rank contraction second operand requires exact equal rank-4 shards")
        x_shard, y_shard = x_shards[0], y_shards[0]
        b, h, q, local_k = x_shard
        m = y_shard[3]
        if x_full != (b, h, q, local_k * k):
            raise RelationCompositionError("K-rank contraction first operand is not exact dim3 sharding")
        if y_full != (b, h, local_k * k, m) or y_shard != (b, h, local_k, m):
            raise RelationCompositionError("K-rank contraction second operand is not exact dim2 sharding")
        if local_k <= 0 or q <= 0 or m <= 0:
            raise RelationCompositionError("K-rank contraction dimensions must be positive")
        expected_output = (b, h, q, m)
        if output != expected_output or any(shape != expected_output for shape in pm_outputs):
            raise RelationCompositionError("K-rank contraction output shape must equal every local contribution")
        declared_sm = tuple(tuple(shape) for shape in sm_step.input_shapes)
        declared_pm = tuple(tuple(tuple(shape) for shape in step.input_shapes) for step in pm_steps)
        if declared_sm != (x_full, y_full) or declared_pm != tuple((x_shard, y_shard) for _ in range(k)):
            raise RelationCompositionError("K-rank contraction declared input shapes disagree with authority")
        first = RelationFactSpec("sharded", (sm_x_ref, *pm_x_refs), gather_dim=3)
        second = RelationFactSpec("sharded", (sm_y_ref, *pm_y_refs), gather_dim=2)
        output_fact = RelationFactSpec("reduction", frontier)
        spec = get_closed_rule_spec("matmul-contraction-reduction-k-rank")
        certificates.append(KRankMatmulContractionCertificate(
            spec.rule_id, k, first, second, output_fact,
            sm_step.step_id, tuple(step.step_id for step in pm_steps),
            x_full, x_shard, y_full, y_shard, output,
            spec.lean_theorems[0],
        ))
        rewritten.extend((first.step_triple, second.step_triple))
        rewritten_layouts.extend(("sharded", "sharded"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankSoftmaxCertificate:
    """Exact dynamic-K rank-4 non-last-axis softmax transport authority."""

    rule_id: str
    rank_count: int
    gather_dim: int
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    lean_theorem: str


def advance_k_rank_softmax_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[KRankSoftmaxCertificate, ...], tuple[tuple[str, ...], ...], tuple[str, ...]]:
    """Pull dim-1/dim-2 rank-4 softmax outputs to the same ordered shard fact."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank softmax frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.op != "FW_softmax" or any(step.op != "FW_softmax" for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        rank_count = len(pm_steps)
        if sm_step.side != "sm" or int(sm_step.rank) != 0 or any(step.side != "pm" for step in pm_steps):
            raise RelationCompositionError("K-rank softmax writers have incompatible side/rank authority")
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank softmax PM writers are not exact ordered ranks")
        writers = (sm_step, *pm_steps)
        if any(tuple(step.parameters) for step in writers):
            raise RelationCompositionError("K-rank FW_softmax writers must declare no parameters")
        if any(len(step.input_bindings) != 1 for step in writers):
            raise RelationCompositionError("K-rank FW_softmax writers must be unary")
        if any(len(step.input_shapes) != 1 for step in writers):
            raise RelationCompositionError("K-rank FW_softmax declared input shape is missing")
        sm_input_ref = sm_step.input_bindings[0]
        pm_input_refs = tuple(step.input_bindings[0] for step in pm_steps)
        try:
            sm_input = by_id[sm_input_ref]
            pm_inputs = tuple(by_id[ref] for ref in pm_input_refs)
        except KeyError as exc:
            raise RelationCompositionError("K-rank softmax input authority is unresolved") from exc
        if sm_input.side != "sm" or any(step.side != "pm" for step in pm_inputs):
            raise RelationCompositionError("K-rank softmax input authority has wrong sides")
        if tuple(int(step.rank) for step in pm_inputs) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank softmax shards do not preserve ordered input authority")
        full_shape = tuple(sm_step.output_shape)
        shard_shapes = tuple(tuple(step.output_shape) for step in pm_steps)
        input_full_shape = tuple(sm_input.output_shape)
        input_shard_shapes = tuple(tuple(step.output_shape) for step in pm_inputs)
        if (len(full_shape) != 4 or not shard_shapes
                or any(len(shape) != 4 or shape != shard_shapes[0] for shape in shard_shapes)):
            raise RelationCompositionError("K-rank softmax outputs require exact equal rank-4 shard shapes")
        shard_shape = shard_shapes[0]
        if input_full_shape != full_shape or input_shard_shapes != shard_shapes:
            raise RelationCompositionError("K-rank softmax input authority shapes must exactly equal output shapes")
        declared_sm = tuple(tuple(shape) for shape in sm_step.input_shapes)
        declared_pm = tuple(tuple(tuple(shape) for shape in step.input_shapes) for step in pm_steps)
        if declared_sm != (full_shape,) or declared_pm != tuple((shard_shape,) for _ in range(rank_count)):
            raise RelationCompositionError("K-rank softmax declared input shapes disagree with authority")
        candidate_dims = tuple(
            dim for dim in (1, 2)
            if full_shape == tuple(
                value * rank_count if index == dim else value
                for index, value in enumerate(shard_shape)
            )
        )
        if len(candidate_dims) != 1:
            # Dim 3 is the normalization axis and is deliberately unsupported.
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        gather_dim = candidate_dims[0]
        input_fact = RelationFactSpec(
            "sharded", (sm_input_ref, *pm_input_refs), gather_dim=gather_dim)
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=gather_dim)
        spec = get_closed_rule_spec(f"softmax-sharded-k-rank-dim{gather_dim}")
        theorem = spec.lean_theorems[0]
        certificates.append(KRankSoftmaxCertificate(
            spec.rule_id, rank_count, gather_dim,
            input_fact, output_fact, sm_step.step_id,
            tuple(step.step_id for step in pm_steps), full_shape, shard_shape, theorem,
        ))
        rewritten.append(input_fact.step_triple)
        rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankDivCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    scalar_param: int
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    lean_theorem: str


def advance_k_rank_div_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[KRankDivCertificate, ...], tuple[tuple[str, ...], ...], tuple[str, ...]]:
    """Pull exact dim-1/dim-2/dim-3 rank-4 FW_div through identical scalar division."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank div frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        # Atomic family: a mixed div/collective frontier remains unresolved.
        if sm_step.op not in ("FW_div", "BW_div") or any(step.op != sm_step.op for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        rank_count = len(pm_steps)
        if sm_step.side != "sm" or int(sm_step.rank) != 0 or any(step.side != "pm" for step in pm_steps):
            raise RelationCompositionError("K-rank div writers have incompatible side/rank authority")
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank div PM writers are not exact ordered ranks")
        writers = (sm_step, *pm_steps)
        if any(len(tuple(step.parameters)) != 1 for step in writers):
            raise RelationCompositionError("K-rank FW_div writers require one scalar parameter")
        params = tuple(int(step.parameters[0]) for step in writers)
        if len(set(params)) != 1:
            raise RelationCompositionError("K-rank FW_div writers require identical scalar parameter")
        expected_arity = 1 if sm_step.op == "FW_div" else 2
        if any(len(step.input_bindings) != expected_arity for step in writers):
            raise RelationCompositionError("K-rank div writers have invalid input arity")
        if any(len(step.input_shapes) != expected_arity for step in writers):
            raise RelationCompositionError("K-rank div writers have invalid declared input arity")
        sm_input = sm_step.input_bindings[0]
        pm_inputs = tuple(step.input_bindings[0] for step in pm_steps)
        try:
            sm_source = by_id[sm_input]
            pm_sources = tuple(by_id[ref] for ref in pm_inputs)
        except KeyError as exc:
            raise RelationCompositionError("K-rank div input authority is unresolved") from exc
        if sm_source.side != "sm" or any(step.side != "pm" for step in pm_sources):
            raise RelationCompositionError("K-rank div input has wrong-side authority")
        if tuple(int(step.rank) for step in pm_sources) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank div input shards are not exact ordered ranks")
        full_shape = tuple(sm_source.output_shape)
        shard_shapes = tuple(tuple(step.output_shape) for step in pm_sources)
        output_full = tuple(sm_step.output_shape)
        output_shards = tuple(tuple(step.output_shape) for step in pm_steps)
        if (len(full_shape) != 4 or not shard_shapes or not output_shards
                or any(len(shape) != 4 or shape != shard_shapes[0] for shape in shard_shapes)
                or len(output_full) != 4
                or any(len(shape) != 4 or shape != output_shards[0] for shape in output_shards)):
            raise RelationCompositionError("K-rank div input sharding requires exact equal rank-4 shapes")
        shard_shape = shard_shapes[0]
        candidates = []
        for axis in (1, 2, 3):
            expected = list(shard_shape); expected[axis] *= rank_count
            if tuple(expected) == full_shape:
                candidates.append(axis)
        if len(candidates) != 1:
            raise RelationCompositionError("K-rank div input sharding is not exact dim1, dim2, or dim3")
        axis = candidates[0]
        if output_full != full_shape or any(shape != shard_shape for shape in output_shards):
            raise RelationCompositionError("K-rank div output shapes/order do not preserve exact sharding")
        declared_sm = tuple(sm_step.input_shapes[0])
        declared_pm = tuple(tuple(step.input_shapes[0]) for step in pm_steps)
        if declared_sm != full_shape or declared_pm != tuple(shard_shape for _ in range(rank_count)):
            raise RelationCompositionError("K-rank div declared input shapes disagree with authority")
        input_fact = RelationFactSpec("sharded", (sm_input, *pm_inputs), gather_dim=axis)
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=axis)
        spec = get_closed_rule_spec(f"div-sharded-k-rank-dim{axis}")
        if sm_step.op != "FW_div" and len(spec.lean_theorems) != 2:
            raise RelationCompositionError(
                f"K-rank BW_div has no registered theorem for axis {axis}"
            )
        theorem = (
            spec.lean_theorems[0] if sm_step.op == "FW_div"
            else spec.lean_theorems[1]
        )
        certificates.append(KRankDivCertificate(
            spec.rule_id, rank_count, axis, params[0],
            input_fact, output_fact, sm_step.step_id,
            tuple(step.step_id for step in pm_steps), full_shape, shard_shape,
            theorem,
        ))
        rewritten.append(input_fact.step_triple)
        rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankLocalRelationCertificate:
    rule_id: str
    op: str
    rank_count: int
    gather_dim: int
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    external_tids: tuple[int, ...]
    external_shapes: tuple[tuple[int, ...], ...]
    lean_theorem: str
    external_facts: tuple[RelationFactSpec, ...] = ()

    @property
    def external_weight_tid(self) -> int:
        if len(self.external_tids) != 1:
            raise RelationCompositionError("local relation does not have exactly one weight")
        return self.external_tids[0]

    @property
    def external_weight_shape(self) -> tuple[int, ...]:
        if len(self.external_shapes) != 1:
            raise RelationCompositionError("local relation does not have exactly one weight shape")
        return self.external_shapes[0]


@dataclass(frozen=True)
class ClosedRuleSpec:
    """Canonical identity/backend binding for one closed proof rule."""

    rule_id: str
    certificate_type: type
    lean_theorems: tuple[str, ...]
    op: str | None
    singleton_renderer: str | None
    lean_imports: tuple[str, ...] = ()



def get_closed_rule_spec(rule_id: str) -> ClosedRuleSpec:
    try:
        return CLOSED_RULE_REGISTRY[rule_id]
    except KeyError as exc:
        raise RelationCompositionError(f"unregistered closed rule identity: {rule_id}") from exc


@dataclass(frozen=True)
class KRankContiguousRelationCertificate:
    """Exact authority for one SM and K ordered PM contiguous writers."""

    rule_id: str
    rank_count: int
    gather_dim: int
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


@dataclass(frozen=True)
class KRankTransposeRelationCertificate:
    """Exact authority for one SM and K ordered PM checked rank-4 transposes."""

    rule_id: str
    rank_count: int
    parameters: tuple[int, int]
    input_gather_dim: int
    output_gather_dim: int
    input_full_shape: tuple[int, ...]
    input_shard_shape: tuple[int, ...]
    output_full_shape: tuple[int, ...]
    output_shard_shape: tuple[int, ...]
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def _advance_k_rank_local_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
    *,
    op: str,
    input_count: int,
    rule_id: str,
    lean_theorem: str,
    allowed_gather_dims: tuple[int, ...] | None,
    required_rank_count: int | None = None,
    required_tensor_rank: int | None = 3,
) -> tuple[
    tuple[KRankLocalRelationCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError(f"K-rank {op} frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        k = len(frontier) - 1
        if required_rank_count is not None and k != required_rank_count:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if sm_step.side != "sm" or sm_step.op != op:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if any(step.side != "pm" or step.op != op for step in pm_steps):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(k)):
            raise RelationCompositionError(f"K-rank {op} PM writers are not ordered ranks 0..K-1")
        if len(sm_step.input_bindings) != input_count or any(
            len(step.input_bindings) != input_count for step in pm_steps
        ):
            raise RelationCompositionError(f"K-rank {op} input arity mismatch")
        external_columns = tuple(
            (sm_step.input_bindings[index], *(step.input_bindings[index] for step in pm_steps))
            for index in range(1, input_count)
        )
        external_refs = []
        external_facts = []
        for refs in external_columns:
            sm_ref, *pm_refs = refs
            if not sm_ref.startswith("init:") or len(set(pm_refs)) != 1:
                rewritten.append(frontier)
                rewritten_layouts.append(layout)
                break
            pm_ref = pm_refs[0]
            if pm_ref == sm_ref:
                external_refs.append(sm_ref)
                continue
            source = pm_ref
            seen_aliases = set()
            while not source.startswith("init:"):
                if source in seen_aliases or source not in by_id:
                    raise RelationCompositionError(f"K-rank {op} external alias chain is unresolved")
                seen_aliases.add(source)
                alias = by_id[source]
                if (alias.op != "FW_multiref" or len(alias.input_bindings) != 1
                        or len(alias.parameters) != 1
                        or not 0 <= alias.output_index < alias.parameters[0]):
                    raise RelationCompositionError(f"K-rank {op} external source is not a multiref alias")
                source = alias.input_bindings[0]
            if source != sm_ref:
                raise RelationCompositionError(f"K-rank {op} external aliases do not derive from SM authority")
            external_refs.append(sm_ref)
            external_facts.append(RelationFactSpec("joined", (sm_ref,), joined_pm_step=pm_ref))
        else:
            pass
        if len(external_refs) != len(external_columns):
            continue
        if len(getattr(sm_step, "input_shapes", ())) != input_count or any(
            len(getattr(step, "input_shapes", ())) != input_count for step in pm_steps
        ):
            raise RelationCompositionError(f"K-rank {op} external input shapes are missing")
        external_shape_columns = tuple(
            (tuple(sm_step.input_shapes[index]),
             *(tuple(step.input_shapes[index]) for step in pm_steps))
            for index in range(1, input_count)
        )
        if any(len(set(shapes)) != 1 for shapes in external_shape_columns):
            raise RelationCompositionError(f"K-rank {op} external input shapes disagree")
        external_shapes = tuple(shapes[0] for shapes in external_shape_columns)
        external_refs = [refs[0] for refs in external_columns]
        try:
            external_tids = tuple(int(ref.split(":", 1)[1]) for ref in external_refs)
            sm_input = by_id[sm_step.input_bindings[0]]
            pm_inputs = tuple(by_id[step.input_bindings[0]] for step in pm_steps)
        except (KeyError, ValueError) as exc:
            raise RelationCompositionError(f"K-rank {op} source is unresolved: {exc}") from exc
        if sm_input.side != "sm" or any(step.side != "pm" for step in pm_inputs):
            raise RelationCompositionError(f"K-rank {op} source frontier has the wrong side")
        if tuple(int(step.rank) for step in pm_inputs) != tuple(range(k)):
            raise RelationCompositionError(f"K-rank {op} source shards are not rank ordered")

        def gather_dim(full_shape, shard_shapes, label):
            if not shard_shapes or any(tuple(shape) != tuple(shard_shapes[0]) for shape in shard_shapes[1:]):
                raise RelationCompositionError(f"K-rank {op} {label} shard shapes disagree")
            full, shard = tuple(full_shape), tuple(shard_shapes[0])
            if len(full) != len(shard):
                raise RelationCompositionError(f"K-rank {op} full/shard tensor ranks disagree")
            if required_tensor_rank is not None and len(full) != required_tensor_rank:
                raise RelationCompositionError(
                    f"K-rank {op} requires tensor rank {required_tensor_rank}"
                )
            candidates = [
                dim for dim in range(len(full))
                if full[dim] == shard[dim] * k
                and all(full[i] == shard[i] for i in range(len(full)) if i != dim)
            ]
            if len(candidates) != 1:
                raise RelationCompositionError(
                    f"K-rank {op} {label} does not determine one gather dimension: {candidates}"
                )
            return candidates[0]

        input_dim = gather_dim(sm_input.output_shape, tuple(step.output_shape for step in pm_inputs), "input")
        output_dim = gather_dim(sm_step.output_shape, tuple(step.output_shape for step in pm_steps), "output")
        if input_dim != output_dim:
            raise RelationCompositionError(f"K-rank {op} changes the sharding dimension")
        if allowed_gather_dims is not None and input_dim not in allowed_gather_dims:
            raise RelationCompositionError(
                f"K-rank {op} has no registered theorem for gather dimension {input_dim}"
            )
        input_refs = (sm_input.step_id, *(step.step_id for step in pm_inputs))
        output_refs = (sm_step.step_id, *(step.step_id for step in pm_steps))
        certificates.append(KRankLocalRelationCertificate(
            rule_id=rule_id,
            op=op,
            rank_count=k,
            gather_dim=input_dim,
            input_fact=RelationFactSpec("sharded", input_refs, gather_dim=input_dim),
            output_fact=RelationFactSpec("sharded", output_refs, gather_dim=output_dim),
            sm_step_id=sm_step.step_id,
            pm_step_ids=tuple(step.step_id for step in pm_steps),
            external_tids=external_tids,
            external_shapes=external_shapes,
            external_facts=tuple(external_facts),
            lean_theorem=lean_theorem,
        ))
        rewritten.append(input_refs)
        rewritten_layouts.append("sharded")
        for fact in external_facts:
            rewritten.append((fact.step_triple[0], fact.joined_pm_step))
            rewritten_layouts.append("joined")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


def advance_k_rank_linear_relation_frontiers(plan, frontiers, layouts):
    spec = _LINEAR_CLOSED_RULE
    return _advance_k_rank_local_relation_frontiers(
        plan, frontiers, layouts,
        op=spec.op,
        input_count=2,
        rule_id=spec.rule_id,
        lean_theorem=spec.lean_theorems[0],
        allowed_gather_dims=(1,),
    )


def advance_k_rank_rms_norm_relation_frontiers(plan, frontiers, layouts):
    spec = get_closed_rule_spec("rms-norm-sharded-two-rank-dim0")
    return _advance_k_rank_local_relation_frontiers(
        plan, frontiers, layouts,
        op=spec.op,
        input_count=2,
        rule_id=spec.rule_id,
        lean_theorem=spec.lean_theorems[0],
        allowed_gather_dims=(0,),
        required_rank_count=2,
        required_tensor_rank=2,
    )


def advance_k_rank_layernorm_relation_frontiers(plan, frontiers, layouts):
    spec = _LAYERNORM_CLOSED_RULE
    return _advance_k_rank_local_relation_frontiers(
        plan, frontiers, layouts,
        op=spec.op,
        input_count=3,
        rule_id=spec.rule_id,
        lean_theorem=spec.lean_theorems[0],
        allowed_gather_dims=(1,),
    )


def advance_k_rank_gelu_relation_frontiers(plan, frontiers, layouts):
    spec = _GELU_CLOSED_RULE
    return _advance_k_rank_local_relation_frontiers(
        plan, frontiers, layouts,
        op=spec.op,
        input_count=1,
        rule_id=spec.rule_id,
        lean_theorem=spec.lean_theorems[0],
        allowed_gather_dims=None,
    )


def advance_k_rank_mix_linear_relation_frontiers(plan, frontiers, layouts):
    return _advance_k_rank_local_relation_frontiers(
        plan, frontiers, layouts,
        op="FW_mix_precision_linear",
        input_count=2,
        rule_id="mix-linear-sharded-two-rank-dim0",
        lean_theorem="TrainVerify.Denote.RelationCompiler.ShardedRel.fw_linear_dim0_two_2d",
        allowed_gather_dims=(0,),
        required_rank_count=2,
        required_tensor_rank=2,
    )


def advance_k_rank_contiguous_relation_frontiers(plan, frontiers, layouts, *, goal_ir=None):
    """Transport an exact ordered K-rank ShardedRel through FW_contiguous."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank FW_contiguous frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        k = len(frontier) - 1
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.side != "sm" or sm_step.op not in ("FW_contiguous", "BW_contiguous", "FW_float", "FW_reshape", "FW_view"):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if any(step.side != "pm" or step.op != sm_step.op for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(k)):
            raise RelationCompositionError("K-rank FW_contiguous PM writers are not ordered ranks 0..K-1")
        writers = (sm_step, *pm_steps)
        if sm_step.op in {"FW_reshape", "FW_view"}:
            if any(tuple(step.parameters) != tuple(step.output_shape) for step in writers):
                raise RelationCompositionError("K-rank FW_reshape parameters must equal each local output shape")
        elif any(tuple(getattr(step, "parameters", ())) for step in writers):
            raise RelationCompositionError("K-rank contiguous writers require no parameters")
        expected_arity = 1 if sm_step.op in ("FW_contiguous", "FW_float", "FW_reshape", "FW_view") else 2
        if any(len(step.input_bindings) != expected_arity or len(getattr(step, "input_shapes", ())) != expected_arity
               for step in writers):
            raise RelationCompositionError("K-rank contiguous writers have invalid input arity")
        input_refs = tuple(step.input_bindings[0] for step in writers)
        init_sources = all(ref.startswith("init:") for ref in input_refs)
        if init_sources and goal_ir is not None and sm_step.op == "FW_contiguous":
            closed, remaining, _ = close_k_rank_init_authority(goal_ir, (input_refs,), ("sharded",))
            if remaining or len(closed) != 1:
                raise RelationCompositionError("K-rank FW_contiguous requires exact InitGoal source authority")
            from .proof_compiler import compile_proof_plan, build_default_registry
            authentic = compile_proof_plan(goal_ir, build_default_registry())
            authentic_steps = _step_map(authentic)
            if not authentic.supported or any(authentic_steps.get(s.step_id) != s for s in writers):
                raise RelationCompositionError("K-rank FW_contiguous input producer authority mismatch")
        else:
            try:
                inputs = tuple(by_id[ref] for ref in input_refs)
            except KeyError as exc:
                raise RelationCompositionError(f"K-rank FW_contiguous source is unresolved: {exc}") from exc
            if inputs[0].side != "sm" or any(step.side != "pm" for step in inputs[1:]):
                raise RelationCompositionError("K-rank FW_contiguous source frontier has the wrong side")
            if tuple(int(step.rank) for step in inputs[1:]) != tuple(range(k)):
                raise RelationCompositionError("K-rank FW_contiguous source shards are not ordered ranks 0..K-1")
            if any(tuple(writer.input_shapes[0]) != tuple(source.output_shape)
                   for writer, source in zip(writers, inputs)):
                raise RelationCompositionError("K-rank FW_contiguous declared input shape disagrees with its source")
        if any(tuple(writer.output_shape) != tuple(writer.input_shapes[0]) for writer in writers):
            if sm_step.op in {"FW_view", "FW_reshape"}:
                rewritten.append(frontier)
                rewritten_layouts.append(layout)
                continue
            raise RelationCompositionError("K-rank FW_contiguous must be shape preserving")
        full_shape = tuple(sm_step.output_shape)
        shard_shapes = tuple(tuple(step.output_shape) for step in pm_steps)
        if not shard_shapes or any(shape != shard_shapes[0] for shape in shard_shapes[1:]):
            raise RelationCompositionError("K-rank FW_contiguous shard shapes disagree")
        shard_shape = shard_shapes[0]
        if len(full_shape) != len(shard_shape):
            raise RelationCompositionError("K-rank FW_contiguous full/shard ranks disagree")
        candidates = [dim for dim in range(len(full_shape))
                      if full_shape[dim] == shard_shape[dim] * k
                      and all(full_shape[index] == shard_shape[index]
                              for index in range(len(full_shape)) if index != dim)]
        if len(candidates) != 1:
            raise RelationCompositionError(
                f"K-rank FW_contiguous does not determine one gather dimension: {candidates}")
        gather_dim = candidates[0]
        input_fact = RelationFactSpec("sharded", input_refs, gather_dim=gather_dim)
        if init_sources and goal_ir is not None and input_fact != closed[0]:
            raise RelationCompositionError("K-rank FW_contiguous InitGoal gather dimension mismatch")
        output_fact = RelationFactSpec("sharded", tuple(frontier), gather_dim=gather_dim)
        rule_id = (
            "float-sharded-k-rank" if sm_step.op == "FW_float"
            else f"{sm_step.op[3:].lower()}-sharded-k-rank" if sm_step.op in {"FW_reshape", "FW_view"}
            else "contiguous-sharded-k-rank"
        )
        spec = get_closed_rule_spec(rule_id)
        theorem = spec.lean_theorems[0]
        certificates.append(KRankContiguousRelationCertificate(
            rule_id=rule_id, rank_count=k, gather_dim=gather_dim,
            full_shape=full_shape, shard_shape=shard_shape,
            input_fact=input_fact, output_fact=output_fact,
            sm_step_id=sm_step.step_id,
            pm_step_ids=tuple(step.step_id for step in pm_steps),
            lean_theorem=theorem))
        rewritten.append(input_refs); rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


def advance_k_rank_transpose_relation_frontiers(plan, frontiers, layouts):
    """Transport an exact ordered K-rank ShardedRel backward through parameterized transposeAxes."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank FW_transpose frontier/layout arity mismatch")

    def swap_axes(shape, dim0, dim1):
        shape = tuple(shape)
        if dim0 == dim1 or dim0 >= len(shape) or dim1 >= len(shape):
            raise RelationCompositionError("K-rank FW_transpose parameters are not two distinct legal axes")
        values = list(shape)
        values[dim0], values[dim1] = values[dim1], values[dim0]
        return tuple(values)

    def unique_gather_dim(full_shape, shard_shape, k, label):
        if len(full_shape) != len(shard_shape):
            raise RelationCompositionError(f"K-rank FW_transpose {label} full/shard ranks disagree")
        candidates = [
            dim for dim in range(len(full_shape))
            if full_shape[dim] == shard_shape[dim] * k
            and all(full_shape[index] == shard_shape[index]
                    for index in range(len(full_shape)) if index != dim)
        ]
        if len(candidates) != 1:
            raise RelationCompositionError(
                f"K-rank FW_transpose does not determine one {label} gather dimension: {candidates}")
        return candidates[0]

    by_id = {step.step_id: step for step in plan.steps}
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        k = len(frontier) - 1
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.side != "sm" or sm_step.op not in ("FW_transpose", "BW_transpose"):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if any(step.side != "pm" or step.op != sm_step.op for step in pm_steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if int(sm_step.rank) != 0:
            raise RelationCompositionError("K-rank FW_transpose SM writer must have rank 0")
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(k)):
            raise RelationCompositionError("K-rank FW_transpose PM writers are not ordered ranks 0..K-1")
        writers = (sm_step, *pm_steps)
        writer_params = tuple(tuple(getattr(step, "parameters", ())) for step in writers)
        if any(len(params) != 2 for params in writer_params):
            raise RelationCompositionError("K-rank FW_transpose writers require exactly two parameters")
        if any(params != writer_params[0] for params in writer_params[1:]):
            raise RelationCompositionError("K-rank FW_transpose writers require matching parameters")
        expected_arity = 1 if sm_step.op == "FW_transpose" else 2
        if any(len(step.input_bindings) != expected_arity or len(getattr(step, "input_shapes", ())) != expected_arity
               for step in writers):
            raise RelationCompositionError("K-rank transpose writers have invalid input arity")
        try:
            inputs = tuple(by_id[step.input_bindings[0]] for step in writers)
        except KeyError as exc:
            raise RelationCompositionError(f"K-rank FW_transpose source is unresolved: {exc}") from exc
        if inputs[0].side != "sm" or any(step.side != "pm" for step in inputs[1:]):
            raise RelationCompositionError("K-rank FW_transpose source frontier has the wrong side")
        if tuple(int(step.rank) for step in inputs[1:]) != tuple(range(k)):
            raise RelationCompositionError("K-rank FW_transpose source shards are not ordered ranks 0..K-1")
        if any(tuple(writer.input_shapes[0]) != tuple(source.output_shape)
               for writer, source in zip(writers, inputs)):
            raise RelationCompositionError("K-rank FW_transpose declared input shape disagrees with its source")

        output_full_shape = tuple(sm_step.output_shape)
        output_shard_shapes = tuple(tuple(step.output_shape) for step in pm_steps)
        dim0, dim1 = writer_params[0]
        if (dim0, dim1) not in ((1, 2), (2, 3)):
            raise RelationCompositionError(
                "K-rank FW_transpose is outside the checked axis pairs (1, 2) and (2, 3)")
        expected_outputs = tuple(
            swap_axes(tuple(step.input_shapes[0]), dim0, dim1) for step in writers
        )
        if tuple(sm_step.output_shape) != expected_outputs[0] or any(
            tuple(step.output_shape) != expected
            for step, expected in zip(pm_steps, expected_outputs[1:])
        ):
            raise RelationCompositionError("K-rank FW_transpose writer has incompatible transpose output shape")
        if not output_shard_shapes or any(shape != output_shard_shapes[0]
                                          for shape in output_shard_shapes[1:]):
            raise RelationCompositionError("K-rank FW_transpose output shard shapes disagree")
        output_shard_shape = output_shard_shapes[0]
        output_gather_dim = unique_gather_dim(
            output_full_shape, output_shard_shape, k, "output")

        input_full_shape = swap_axes(output_full_shape, dim0, dim1)
        input_shard_shape = swap_axes(output_shard_shape, dim0, dim1)
        if tuple(sm_step.input_shapes[0]) != input_full_shape or any(
            tuple(step.input_shapes[0]) != input_shard_shape for step in pm_steps
        ):
            raise RelationCompositionError("K-rank FW_transpose writer has incompatible transpose output shape")
        input_gather_dim = unique_gather_dim(
            input_full_shape, input_shard_shape, k, "input")
        expected_input_dim = (
            dim1 if output_gather_dim == dim0 else
            dim0 if output_gather_dim == dim1 else
            output_gather_dim
        )
        if input_gather_dim != expected_input_dim:
            raise RelationCompositionError("K-rank FW_transpose gather-axis transport is incompatible")

        input_refs = tuple(step.step_id for step in inputs)
        if len(input_full_shape) != 4 or len(input_shard_shape) != 4:
            raise RelationCompositionError("K-rank FW_transpose is outside the checked rank-4 family")
        theorem_by_axis_transport = {
            ((1, 2), 3, 3): "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim3_rank4",
            ((1, 2), 2, 1): "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim2_to_dim1_rank4",
            ((1, 2), 1, 2): "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_1_2_dim1_to_dim2_rank4",
            ((2, 3), 2, 3): "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim2_to_dim3_rank4",
            ((2, 3), 3, 2): "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim3_to_dim2_rank4",
            ((2, 3), 1, 1): "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_transposeAxes_2_3_dim1_rank4",
        }
        try:
            lean_theorem = theorem_by_axis_transport[
                (writer_params[0], input_gather_dim, output_gather_dim)
            ]
        except KeyError as exc:
            raise RelationCompositionError(
                "K-rank FW_transpose is outside the checked gather-axis pairs") from exc

        input_fact = RelationFactSpec("sharded", input_refs, gather_dim=input_gather_dim)
        output_fact = RelationFactSpec("sharded", tuple(frontier), gather_dim=output_gather_dim)
        certificates.append(KRankTransposeRelationCertificate(
            rule_id="transpose-sharded-k-rank", rank_count=k,
            parameters=writer_params[0],
            input_gather_dim=input_gather_dim, output_gather_dim=output_gather_dim,
            input_full_shape=input_full_shape, input_shard_shape=input_shard_shape,
            output_full_shape=output_full_shape, output_shard_shape=output_shard_shape,
            input_fact=input_fact, output_fact=output_fact,
            sm_step_id=sm_step.step_id,
            pm_step_ids=tuple(step.step_id for step in pm_steps),
            lean_theorem=lean_theorem))
        rewritten.append(input_refs); rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankMultirefRelationCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    projection: int
    pm_projections: tuple[int, ...]
    arity: int
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_multiref_relation_frontiers(plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank multiref frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        k = len(frontier) - 1
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if sm_step.side != "sm" or sm_step.op != "FW_multiref" or any(
            step.side != "pm" or step.op != "FW_multiref" for step in pm_steps
        ):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(k)):
            raise RelationCompositionError("K-rank FW_multiref writers are not ordered ranks 0..K-1")
        steps = (sm_step, *pm_steps)
        if any(len(step.input_bindings) != 1 for step in steps):
            raise RelationCompositionError("K-rank FW_multiref requires one input")
        params = {tuple(step.parameters) for step in steps}
        projections = tuple(int(step.output_index) for step in steps)
        if len(params) != 1 or len(next(iter(params))) != 1:
            raise RelationCompositionError("K-rank FW_multiref arity parameters disagree")
        arity = int(next(iter(params))[0])
        projection = projections[0]
        pm_projections = projections[1:]
        if arity <= 0 or any(not 0 <= output < arity for output in projections):
            raise RelationCompositionError("K-rank FW_multiref projection is out of bounds")
        try:
            sm_input = by_id[sm_step.input_bindings[0]]
            pm_inputs = tuple(by_id[step.input_bindings[0]] for step in pm_steps)
        except KeyError as exc:
            raise RelationCompositionError(f"K-rank FW_multiref source is unresolved: {exc}") from exc
        if sm_input.side != "sm" or tuple(int(step.rank) for step in pm_inputs) != tuple(range(k)):
            raise RelationCompositionError("K-rank FW_multiref source frontier has invalid sides/ranks")
        input_refs = (sm_input.step_id, *(step.step_id for step in pm_inputs))
        output_refs = (sm_step.step_id, *(step.step_id for step in pm_steps))
        full_in, shard_in = tuple(sm_input.output_shape), tuple(pm_inputs[0].output_shape)
        if any(tuple(step.output_shape) != shard_in for step in pm_inputs):
            raise RelationCompositionError("K-rank FW_multiref input shard shapes disagree")
        candidates = [dim for dim in range(len(full_in)) if full_in[dim] == shard_in[dim] * k and all(full_in[j] == shard_in[j] for j in range(len(full_in)) if j != dim)]
        if len(candidates) != 1:
            raise RelationCompositionError(f"K-rank FW_multiref does not determine one gather dimension: {candidates}")
        dim = candidates[0]
        if tuple(sm_step.output_shape) != full_in or any(tuple(step.output_shape) != shard_in for step in pm_steps):
            raise RelationCompositionError("K-rank FW_multiref is not shape preserving")
        certificates.append(KRankMultirefRelationCertificate(
            rule_id="multiref-sharded-k-rank", rank_count=k, gather_dim=dim,
            projection=projection, pm_projections=pm_projections, arity=arity,
            input_fact=RelationFactSpec("sharded", input_refs, gather_dim=dim),
            output_fact=RelationFactSpec("sharded", output_refs, gather_dim=dim),
            sm_step_id=sm_step.step_id,
            pm_step_ids=tuple(step.step_id for step in pm_steps),
            lean_theorem="TrainVerify.Denote.applyNode_fw_multiref_at",
        ))
        rewritten.append(input_refs); rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBinaryRelationCertificate:
    rule_id: str
    op: str
    rank_count: int
    gather_dim: int
    input_facts: tuple[RelationFactSpec, RelationFactSpec]
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


_CLOSED_RULE_SPECS = (
    ClosedRuleSpec(
        rule_id="linear-sharded-k-rank-dim1",
        certificate_type=KRankLocalRelationCertificate,
        lean_theorems=("TrainVerify.Denote.fw_linear_3d_allGatherPrimDimN_dim1_comm",),
        op="FW_linear",
        singleton_renderer=(
            "sparse_local_linear_renderer:"
            "render_closed_sparse_k_rank_local_linear_segment"
        ),
    ),
    ClosedRuleSpec(
        rule_id="layernorm-sharded-k-rank-dim1",
        certificate_type=KRankLocalRelationCertificate,
        lean_theorems=(
            "TrainVerify.Denote.fw_layernorm_distribute_allGatherPrimDimN_dim1_K_3d",
        ),
        op="FW_layernorm",
        singleton_renderer=(
            "sparse_layernorm_renderer:render_closed_sparse_k_rank_layernorm_segment"
        ),
    ),
    ClosedRuleSpec(
        rule_id="gelu-sharded-k-rank",
        certificate_type=KRankLocalRelationCertificate,
        lean_theorems=("TrainVerify.Denote.fw_gelu_allGatherPrimDimN_eq",),
        op="FW_gelu",
        singleton_renderer="sparse_gelu_renderer:render_closed_sparse_k_rank_gelu_segment",
    ),
    ClosedRuleSpec(
        rule_id="rms-norm-sharded-two-rank-dim0",
        certificate_type=KRankLocalRelationCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_rms_norm_2d",
        ),
        op="FW_rms_norm",
        singleton_renderer=(
            "rms_norm_sharded_renderer:render_closed_two_rank_rms_norm_segment"
        ),
    ),
    ClosedRuleSpec(
        rule_id="linear-output-sharded-k-rank",
        certificate_type=KRankOutputShardedLinearCertificate,
        lean_theorems=(
            "TrainVerify.Denote.fw_linear_3d_weight_allGatherPrimDimN_dim0_comm",
        ),
        op="FW_linear",
        singleton_renderer=(
            "sparse_output_linear_renderer:"
            "render_closed_sparse_output_sharded_linear_segment"
        ),
        lean_imports=("denote.KRankLinearGather",),
    ),
    ClosedRuleSpec(
        rule_id="add-sharded-k-rank",
        certificate_type=KRankBinaryRelationCertificate,
        lean_theorems=("TrainVerify.Denote.fw_add_allGather_dim_K",),
        op="FW_add",
        singleton_renderer="add_renderer:render_closed_k_rank_add_segment",
        lean_imports=("denote.KRankAddGather",),
    ),
    ClosedRuleSpec(
        rule_id="embedding-sharded-ids-k-rank",
        certificate_type=KRankShardedIdsEmbeddingCertificate,
        lean_theorems=(
            "TrainVerify.Denote.fw_embedding_allGatherPrimDimN_dim1_shared_weight",
        ),
        op=None,
        singleton_renderer=(
            "sharded_ids_embedding_renderer:"
            "render_closed_k_rank_sharded_ids_embedding_segment"
        ),
        lean_imports=("denote.EmbeddingSequenceShard", "denote.KRankAllToAll"),
    ),
    ClosedRuleSpec(
        rule_id="matmul-output-axis-sharded-k-rank-dim3",
        certificate_type=KRankMatmulOutputAxisCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_output_axis_rank4",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_matmul_output_axis_segment",
        lean_imports=("denote.KRankMatmul",),
    ),
    ClosedRuleSpec(
        rule_id="matmul-head-axis-sharded-k-rank-dim1",
        certificate_type=KRankMatmulHeadAxisCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_head_axis_rank4",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_matmul_head_axis_segment",
        lean_imports=("denote.KRankMatmulHeadAxis",),
    ),
    ClosedRuleSpec(
        rule_id="matmul-query-axis-sharded-k-rank-dim2",
        certificate_type=KRankMatmulQueryAxisCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_matmul_query_axis_segment",
        lean_imports=("denote.KRankMatmulQueryAxis",),
    ),
    ClosedRuleSpec(
        rule_id="matmul-contraction-reduction-k-rank",
        certificate_type=KRankMatmulContractionCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_contraction_axis_rank4",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_matmul_contraction_segment",
        lean_imports=("denote.KRankMatmulContractionReduction",),
    ),
    ClosedRuleSpec(
        rule_id="softmax-sharded-k-rank-dim1",
        certificate_type=KRankSoftmaxCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_softmax_dim1_rank4",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_softmax_segment",
        lean_imports=("denote.KRankSoftmaxGather",),
    ),
    ClosedRuleSpec(
        rule_id="softmax-sharded-k-rank-dim2",
        certificate_type=KRankSoftmaxCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_softmax_dim2_rank4",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_softmax_segment",
        lean_imports=("denote.KRankSoftmaxGather",),
    ),
    ClosedRuleSpec(
        rule_id="div-sharded-k-rank-dim1",
        certificate_type=KRankDivCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_div_dim1_rank4",
            "TrainVerify.Denote.bw_div_allGatherPrimDimN_eq_g128",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_div_segment",
        lean_imports=("denote.KRankDivGather",),
    ),
    ClosedRuleSpec(
        rule_id="div-sharded-k-rank-dim2",
        certificate_type=KRankDivCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_div_dim2_rank4",
            "TrainVerify.Denote.bw_div_allGatherPrimDimN_eq_g128",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_div_segment",
        lean_imports=("denote.KRankDivGather",),
    ),
    ClosedRuleSpec(
        rule_id="div-sharded-k-rank-dim3",
        certificate_type=KRankDivCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_div_dim3_rank4",
            "TrainVerify.Denote.bw_div_allGatherPrimDimN_eq_g128",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_div_segment",
        lean_imports=("denote.KRankDivGather",),
    ),
    ClosedRuleSpec(
        rule_id="contiguous-sharded-k-rank",
        certificate_type=KRankContiguousRelationCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_contiguous",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_contiguous_segment",
    ),
    ClosedRuleSpec(
        rule_id="float-sharded-k-rank",
        certificate_type=KRankContiguousRelationCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_contiguous",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_contiguous_segment",
    ),
    ClosedRuleSpec(
        rule_id="reshape-sharded-k-rank",
        certificate_type=KRankContiguousRelationCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_view_id",
        ),
        op="FW_reshape",
        singleton_renderer=(
            "sharded_identity_renderer:render_closed_sharded_identity_segment"
        ),
    ),
    ClosedRuleSpec(
        rule_id="view-sharded-k-rank",
        certificate_type=KRankContiguousRelationCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_view_id",
        ),
        op="FW_view",
        singleton_renderer=(
            "sharded_identity_renderer:render_closed_sharded_identity_segment"
        ),
    ),
    ClosedRuleSpec(
        rule_id="full-producer-chunks-k-rank",
        certificate_type=KRankFullProducerChunksCertificate,
        lean_theorems=("TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn",),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_full_producer_chunks_segment",
    ),
    ClosedRuleSpec(
        rule_id="allgather-reconstruction-k-rank",
        certificate_type=KRankAllGatherReconstructionCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ShardedRel.to_joined_allGather",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_allgather_segment",
    ),
    ClosedRuleSpec(
        rule_id="allreduce-reconstruction-k-rank",
        certificate_type=KRankAllReduceReconstructionCertificate,
        lean_theorems=(
            "TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_allreduce_segment",
    ),
    ClosedRuleSpec(
        rule_id="embedding-vocab-sharded-reduction-k-rank",
        certificate_type=KRankVocabShardedEmbeddingProducerCertificate,
        lean_theorems=("TrainVerify.Denote.fw_embedding_eq_allReduce_offset_shards",),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_vocab_embedding_segment",
    ),
    ClosedRuleSpec(
        rule_id="sum-producer-sharded-k-rank-dim1",
        certificate_type=KRankSumProducerCertificate,
        lean_theorems=(
            "TrainVerify.Denote.fw_sum_allGatherPrimDimN_eq_allReducePrim_fw_sum",
        ),
        op=None,
        singleton_renderer="composer:render_closed_k_rank_sum_producer_segment",
    ),
    ClosedRuleSpec(
        rule_id="embedding-hidden-sharded-k-rank",
        certificate_type=KRankHiddenShardedEmbeddingCertificate,
        lean_theorems=(
            "TrainVerify.Denote.fw_embedding_hidden_shards_two",
            "TrainVerify.Denote.fw_embedding_hidden_shards_k_rank",
        ),
        op=None,
        singleton_renderer=(
            "hidden_sharded_embedding_renderer:"
            "render_closed_k_rank_hidden_sharded_embedding_segment"
        ),
    ),
)

CLOSED_RULE_REGISTRY: dict[str, ClosedRuleSpec] = {
    spec.rule_id: spec for spec in _CLOSED_RULE_SPECS
}
if len(CLOSED_RULE_REGISTRY) != len(_CLOSED_RULE_SPECS):
    raise RuntimeError("closed rule registry contains duplicate identities")


def _register_closed_rule_specs(*specs: ClosedRuleSpec) -> None:
    for spec in specs:
        if spec.rule_id in CLOSED_RULE_REGISTRY:
            raise RuntimeError(f"duplicate closed rule identity: {spec.rule_id}")
        CLOSED_RULE_REGISTRY[spec.rule_id] = spec


_LINEAR_CLOSED_RULE = CLOSED_RULE_REGISTRY["linear-sharded-k-rank-dim1"]
_LAYERNORM_CLOSED_RULE = CLOSED_RULE_REGISTRY["layernorm-sharded-k-rank-dim1"]
_GELU_CLOSED_RULE = CLOSED_RULE_REGISTRY["gelu-sharded-k-rank"]


def advance_k_rank_add_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankBinaryRelationCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank add frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates = []
    rewritten = []
    rewritten_layouts = []

    def infer_dim(full_shape, shard_shapes, k, label):
        if not shard_shapes or any(tuple(shape) != tuple(shard_shapes[0]) for shape in shard_shapes[1:]):
            raise RelationCompositionError(f"K-rank FW_add {label} shard shapes disagree")
        full, shard = tuple(full_shape), tuple(shard_shapes[0])
        if len(full) != len(shard):
            raise RelationCompositionError(f"K-rank FW_add {label} ranks disagree")
        candidates = [
            dim for dim in range(len(full))
            if full[dim] == shard[dim] * k
            and all(full[index] == shard[index] for index in range(len(full)) if index != dim)
        ]
        if len(candidates) != 1:
            raise RelationCompositionError(
                f"K-rank FW_add {label} does not determine one gather dimension: {candidates}"
            )
        return candidates[0]

    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded" or len(frontier) < 3:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        k = len(frontier) - 1
        try:
            sm_step = by_id[frontier[0]]
            pm_steps = tuple(by_id[ref] for ref in frontier[1:])
        except KeyError:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if sm_step.side != "sm" or sm_step.op not in {"FW_add", "FW_swiglu", "FW_glu"}:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        operator = sm_step.op
        if any(step.side != "pm" or step.op != operator for step in pm_steps):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if tuple(int(step.rank) for step in pm_steps) != tuple(range(k)):
            raise RelationCompositionError("K-rank FW_add PM writers are not ordered ranks 0..K-1")
        if len(sm_step.input_bindings) != 2 or any(len(step.input_bindings) != 2 for step in pm_steps):
            raise RelationCompositionError("K-rank FW_add requires exactly two dynamic inputs")
        input_frontiers = []
        input_dims = []
        for argument in range(2):
            try:
                sm_input = by_id[sm_step.input_bindings[argument]]
                pm_inputs = tuple(by_id[step.input_bindings[argument]] for step in pm_steps)
            except KeyError as exc:
                raise RelationCompositionError(
                    f"K-rank FW_add argument {argument} source is unresolved: {exc}"
                ) from exc
            if sm_input.side != "sm" or any(step.side != "pm" for step in pm_inputs):
                raise RelationCompositionError(f"K-rank FW_add argument {argument} has the wrong side")
            if tuple(int(step.rank) for step in pm_inputs) != tuple(range(k)):
                raise RelationCompositionError(
                    f"K-rank FW_add argument {argument} shards are not rank ordered"
                )
            refs = (sm_input.step_id, *(step.step_id for step in pm_inputs))
            input_frontiers.append(refs)
            input_dims.append(infer_dim(
                sm_input.output_shape,
                tuple(step.output_shape for step in pm_inputs),
                k,
                f"argument {argument}",
            ))
        output_dim = infer_dim(
            sm_step.output_shape,
            tuple(step.output_shape for step in pm_steps),
            k,
            "output",
        )
        if input_dims != [output_dim, output_dim]:
            raise RelationCompositionError(
                f"K-rank FW_add changes sharding dimension: inputs={input_dims}, output={output_dim}"
            )
        output_refs = (sm_step.step_id, *(step.step_id for step in pm_steps))
        input_facts = tuple(
            RelationFactSpec("sharded", refs, gather_dim=output_dim)
            for refs in input_frontiers
        )
        if operator == "FW_swiglu":
            full_shape = tuple(sm_step.output_shape)
            shard_shape = tuple(pm_steps[0].output_shape)
            if (k != 2 or len(full_shape) != 2 or len(shard_shape) != 2
                    or min(shard_shape) <= 0):
                raise RelationCompositionError("K-rank FW_swiglu requires two positive matrix shards")
            if output_dim == 1 and full_shape == (shard_shape[0], shard_shape[1] * 2):
                rule_id = "swiglu-sharded-two-rank-dim1"
                lean_theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_swiglu_dim1_two_2d"
            elif output_dim == 0 and full_shape == (shard_shape[0] * 2, shard_shape[1]):
                rule_id = "swiglu-sharded-two-rank-dim0"
                lean_theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_swiglu_dim0_two_2d"
            else:
                raise RelationCompositionError("K-rank FW_swiglu shape/gather orientation is unsupported")
        elif operator == "FW_glu":
            full_shape = tuple(sm_step.output_shape)
            shard_shape = tuple(pm_steps[0].output_shape)
            if (k != 2 or output_dim != 0 or len(full_shape) != 2
                    or len(shard_shape) != 2 or full_shape != (shard_shape[0] * 2, shard_shape[1])
                    or min(shard_shape) <= 0):
                raise RelationCompositionError("K-rank FW_glu requires two positive dim-0 matrix shards")
            rule_id = "glu-sharded-two-rank-dim0"
            lean_theorem = "TrainVerify.Denote.RelationCompiler.ShardedRel.fw_glu_dim0_two_2d"
        else:
            spec = get_closed_rule_spec("add-sharded-k-rank")
            rule_id = spec.rule_id
            lean_theorem = spec.lean_theorems[0]
        certificates.append(KRankBinaryRelationCertificate(
            rule_id=rule_id,
            op=operator,
            rank_count=k,
            gather_dim=output_dim,
            input_facts=input_facts,
            output_fact=RelationFactSpec("sharded", output_refs, gather_dim=output_dim),
            sm_step_id=sm_step.step_id,
            pm_step_ids=tuple(step.step_id for step in pm_steps),
            lean_theorem=lean_theorem,
        ))
        rewritten.extend(input_frontiers)
        rewritten_layouts.extend(("sharded", "sharded"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWSoftmaxCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    gradient_fact: RelationFactSpec
    activation_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_softmax_frontiers(plan, frontiers, layouts):
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("K-rank BW_softmax frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="sharded" or len(frontier)!=5:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_softmax" or sm.side!="sm" or any(x.op!="BW_softmax" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if tuple(int(x.rank) for x in pms)!=(0,1,2,3) or len(sm.input_bindings)!=2 or any(len(x.input_bindings)!=2 for x in pms):
            raise RelationCompositionError("rank-4 BW_softmax writer/input authority mismatch")
        full=tuple(sm.output_shape);shards=tuple(tuple(x.output_shape) for x in pms)
        if full!=(1,4,8,8) or any(x!=shards[0] for x in shards):
            raise RelationCompositionError("BW_softmax output is outside checked rank-4 shapes")
        shard=shards[0]
        candidates=[d for d in (1,2) if full[d]==shard[d]*4 and all(full[i]==shard[i] for i in range(4) if i!=d)]
        if len(candidates)!=1: raise RelationCompositionError(f"BW_softmax axis is not unique orthogonal sharding: {candidates}")
        dim=candidates[0]
        if any(tuple(shape)!=full for shape in sm.input_shapes) or any(any(tuple(shape)!=shard for shape in x.input_shapes) for x in pms):
            raise RelationCompositionError("BW_softmax input shapes do not preserve output sharding")
        grefs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        yrefs=(sm.input_bindings[1],*(x.input_bindings[1] for x in pms))
        gfact=RelationFactSpec("sharded",grefs,gather_dim=dim)
        yfact=RelationFactSpec("sharded",yrefs,gather_dim=dim)
        output=RelationFactSpec("sharded",tuple(frontier),gather_dim=dim)
        theorem=("TrainVerify.Denote.softmaxBwd_split_dim1_4_1_4_8_8_g234" if dim==1
                 else "TrainVerify.Denote.bw_softmax_distribute_allGatherPrimDimN_dim2_4_1_4_2_8_g164")
        certs.append(KRankBWSoftmaxCertificate(
            rule_id=f"bw-softmax-sharded-dim{dim}-rank4",rank_count=4,gather_dim=dim,
            gradient_fact=gfact,activation_fact=yfact,output_fact=output,
            sm_step_id=sm.step_id,pm_step_ids=tuple(x.step_id for x in pms),lean_theorem=theorem))
        rewritten.extend((grefs,yrefs));rewritten_layouts.extend(("sharded","sharded"))
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class JoinedBWViewCertificate:
    rule_id: str
    input_shape: tuple[int, ...]
    target_shape: tuple[int, ...]
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_id: str
    lean_theorem: str


def advance_joined_bw_view_frontiers(plan, frontiers, layouts):
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("joined BW_view frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="joined" or len(frontier)!=2:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pm=by_id[frontier[1]]
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_view" or pm.op!="BW_view" or sm.side!="sm" or pm.side!="pm":
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if len(sm.input_bindings)!=2 or len(pm.input_bindings)!=2 or tuple(sm.parameters)!=tuple(pm.parameters):
            raise RelationCompositionError("joined BW_view operator authority mismatch")
        input_shape=tuple(sm.input_shapes[0]);target_shape=tuple(sm.output_shape)
        if tuple(pm.input_shapes[0])!=input_shape or tuple(pm.output_shape)!=target_shape or tuple(sm.parameters)!=target_shape:
            raise RelationCompositionError("joined BW_view shape/parameter authority mismatch")
        input_frontier=(sm.input_bindings[0],pm.input_bindings[0])
        input_fact=RelationFactSpec("joined",(input_frontier[0],),joined_pm_step=input_frontier[1])
        output_fact=RelationFactSpec("joined",(sm.step_id,),joined_pm_step=pm.step_id)
        certs.append(JoinedBWViewCertificate(
            rule_id="bw-view-joined",input_shape=input_shape,target_shape=target_shape,
            input_fact=input_fact,output_fact=output_fact,sm_step_id=sm.step_id,pm_step_id=pm.step_id,
            lean_theorem="TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view"))
        rewritten.append(input_frontier);rewritten_layouts.append("joined")
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWSumCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    gradient_fact: RelationFactSpec
    activation_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_sum_frontiers(plan, ir, frontiers, layouts):
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("K-rank BW_sum frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="sharded" or len(frontier)<3:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_sum" or sm.side!="sm" or any(x.op!="BW_sum" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        k=len(pms)
        if (int(sm.rank)!=0 or tuple(int(x.rank) for x in pms)!=tuple(range(k))
                or len(sm.input_bindings)!=2 or any(len(x.input_bindings)!=2 for x in pms)):
            raise RelationCompositionError("K-rank BW_sum writer/input authority mismatch")
        if tuple(sm.parameters or ()) or any(tuple(x.parameters or ()) for x in pms):
            raise RelationCompositionError("K-rank BW_sum writers require no parameters")
        full=tuple(sm.output_shape);shards=tuple(tuple(x.output_shape) for x in pms)
        if not shards or any(shape!=shards[0] for shape in shards):
            raise RelationCompositionError("K-rank BW_sum output shard shapes disagree")
        shard=shards[0]
        if (len(full)!=3 or len(shard)!=3 or any(value<=0 for value in shard)
                or full[2]!=shard[2]*k
                or full[:2]!=shard[:2]):
            raise RelationCompositionError("BW_sum is outside checked dim-2 theorem domain")
        sm_inputs=tuple(tuple(shape) for shape in sm.input_shapes)
        pm_inputs=tuple(tuple(tuple(shape) for shape in x.input_shapes) for x in pms)
        if sm_inputs!=((1,),full) or any(shapes!=((1,),shard) for shapes in pm_inputs):
            raise RelationCompositionError("K-rank BW_sum input shapes do not match outputs")
        grefs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        if len(set(grefs))!=1 or not grefs[0].startswith("init:"):
            raise RelationCompositionError("BW_sum scalar gradient is not one shared InitGoal")
        tid=int(grefs[0].split(":",1)[1]);lineage=ir.init_lineages.get(tid)
        if lineage is None: raise RelationCompositionError("BW_sum scalar InitGoal is missing")
        gfact=init_lineage_relation_fact(lineage)
        if gfact.layout!="reduction" or gfact.step_triple!=(grefs[0],grefs[0]):
            raise RelationCompositionError("BW_sum scalar InitGoal is not exact reduction authority")
        xrefs=(sm.input_bindings[1],*(x.input_bindings[1] for x in pms))
        xfact=RelationFactSpec("sharded",xrefs,gather_dim=2)
        output=RelationFactSpec("sharded",tuple(frontier),gather_dim=2)
        certs.append(KRankBWSumCertificate(
            rule_id="bw-sum-scalar-broadcast-dim2-k-rank",rank_count=k,gather_dim=2,
            gradient_fact=gfact,activation_fact=xfact,output_fact=output,
            sm_step_id=sm.step_id,pm_step_ids=tuple(x.step_id for x in pms),
            lean_theorem="TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3"))
        rewritten.extend((gfact.step_triple,xrefs));rewritten_layouts.extend((gfact.layout,"sharded"))
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWGeluCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    gradient_fact: RelationFactSpec
    activation_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_gelu_frontiers(plan, frontiers, layouts):
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("K-rank BW_gelu frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="sharded" or len(frontier)<2:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_gelu" or sm.side!="sm" or any(x.op!="BW_gelu" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        k=len(pms)
        if tuple(int(x.rank) for x in pms)!=tuple(range(k)) or len(sm.input_bindings)!=2 or any(len(x.input_bindings)!=2 for x in pms):
            raise RelationCompositionError("K-rank BW_gelu writer/input authority mismatch")
        full=tuple(sm.output_shape);shards=tuple(tuple(x.output_shape) for x in pms)
        if not shards or any(x!=shards[0] for x in shards):
            raise RelationCompositionError("K-rank BW_gelu output shard shapes disagree")
        shard=shards[0]
        candidates=[d for d in range(len(full)) if full[d]==shard[d]*k and all(full[i]==shard[i] for i in range(len(full)) if i!=d)]
        if len(candidates)!=1: raise RelationCompositionError(f"K-rank BW_gelu axis is ambiguous: {candidates}")
        dim=candidates[0]
        if tuple(sm.input_shapes)!=(full,full) or any(tuple(x.input_shapes)!=(shard,shard) for x in pms):
            raise RelationCompositionError("K-rank BW_gelu input shapes do not preserve output sharding")
        grefs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        xrefs=(sm.input_bindings[1],*(x.input_bindings[1] for x in pms))
        gfact=RelationFactSpec("sharded",grefs,gather_dim=dim)
        xfact=RelationFactSpec("sharded",xrefs,gather_dim=dim)
        output=RelationFactSpec("sharded",tuple(frontier),gather_dim=dim)
        certs.append(KRankBWGeluCertificate(
            rule_id="bw-gelu-pointwise-sharded-k-rank",rank_count=k,gather_dim=dim,
            gradient_fact=gfact,activation_fact=xfact,output_fact=output,
            sm_step_id=sm.step_id,pm_step_ids=tuple(x.step_id for x in pms),
            lean_theorem="TrainVerify.Denote.bw_gelu_allGatherPrimDimN_eq"))
        rewritten.extend((grefs,xrefs));rewritten_layouts.extend(("sharded","sharded"))
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWMatmulCertificate:
    rule_id: str
    family: str
    projection: str
    rank_count: int
    input_facts: tuple[RelationFactSpec, ...]
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_matmul_frontiers(plan, frontiers, layouts):
    """Classify BW_matmul projections by exact operand and output relations."""
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("K-rank BW_matmul frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    def input_relation(sm, pms, argument, k):
        sm_ref=sm.input_bindings[argument];pm_refs=tuple(x.input_bindings[argument] for x in pms)
        full=tuple(sm.input_shapes[argument]);shards=tuple(tuple(x.input_shapes[argument]) for x in pms)
        if any(x!=shards[0] for x in shards):
            raise RelationCompositionError("BW_matmul operand shard shapes disagree")
        if len(set(pm_refs))==1 and shards[0]==full:
            fact=RelationFactSpec("joined",(sm_ref,),joined_pm_step=pm_refs[0])
            return fact,(sm_ref,pm_refs[0]),("joined",None)
        candidates=[d for d in range(len(full)) if full[d]==shards[0][d]*k and all(full[i]==shards[0][i] for i in range(len(full)) if i!=d)]
        if len(candidates)!=1:
            raise RelationCompositionError(f"BW_matmul operand {argument} relation is ambiguous: {candidates}")
        dim=candidates[0];refs=(sm_ref,*pm_refs)
        return RelationFactSpec("sharded",refs,gather_dim=dim),refs,("sharded",dim)
    for frontier,layout in zip(frontiers,layouts):
        if layout not in ("sharded","reduction") or len(frontier)!=5:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_matmul" or sm.side!="sm" or any(x.op!="BW_matmul" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        k=len(pms)
        if k!=4 or tuple(int(x.rank) for x in pms)!=(0,1,2,3) or len(sm.input_bindings)!=3 or any(len(x.input_bindings)!=3 for x in pms):
            raise RelationCompositionError("rank-4 BW_matmul writer/input authority mismatch")
        if sm.output_projection not in (".1",".2") or any(x.output_projection!=sm.output_projection for x in pms):
            raise RelationCompositionError("BW_matmul output projection authority mismatch")
        facts=[];input_frontiers=[];relations=[]
        for argument in range(3):
            fact,input_frontier,relation=input_relation(sm,pms,argument,k)
            facts.append(fact);input_frontiers.append(input_frontier);relations.append(relation)
        full=tuple(sm.output_shape);shards=tuple(tuple(x.output_shape) for x in pms)
        if any(x!=shards[0] for x in shards): raise RelationCompositionError("BW_matmul output shard shapes disagree")
        if layout=="sharded":
            candidates=[d for d in range(len(full)) if full[d]==shards[0][d]*k and all(full[i]==shards[0][i] for i in range(len(full)) if i!=d)]
            if len(candidates)!=1: raise RelationCompositionError(f"BW_matmul output axis is ambiguous: {candidates}")
            out_dim=candidates[0]
        else:
            if any(x!=full for x in shards): raise RelationCompositionError("BW_matmul reduction pieces are not full-shaped")
            out_dim=None
        sig=(sm.output_projection,tuple(relations),layout,out_dim)
        family_theorem={
            (".1",(("joined",None),("sharded",3),("sharded",2)),"sharded",3):
                ("fst-y-sharded","TrainVerify.Denote.bw_matmul_fst_split_1_4_8_8"),
            (".2",(("joined",None),("sharded",3),("sharded",2)),"sharded",2):
                ("snd-x-sharded","TrainVerify.Denote.bw_matmul_snd_split_dX_1_4_8_8"),
            (".1",(("sharded",3),("joined",None),("sharded",3)),"reduction",None):
                ("fst-contraction-reduction","TrainVerify.Denote.bw_matmul_fst_split_dW_1_4_8_8"),
            (".2",(("sharded",3),("joined",None),("sharded",3)),"sharded",3):
                ("snd-g-sharded","TrainVerify.Denote.bw_matmul_snd_split_1_4_8_8"),
            (".1",(("sharded",1),("sharded",1),("sharded",1)),"sharded",1):
                ("batch-sharded","TrainVerify.Denote.bw_matmul_fst_split_dim1_4_1_4_8_8"),
            (".2",(("sharded",1),("sharded",1),("sharded",1)),"sharded",1):
                ("batch-sharded","TrainVerify.Denote.bw_matmul_snd_split_batchdim1_1_4_8_8"),
            (".1",(("sharded",2),("sharded",2),("joined",None)),"sharded",2):
                ("fst-query-sharded","TrainVerify.Denote.RelationCompiler.ShardedRel.fw_matmul_query_axis_rank4"),
            (".2",(("sharded",2),("sharded",2),("joined",None)),"reduction",None):
                ("snd-contraction-reduction","TrainVerify.Denote.bw_matmul_snd_split_dW_g197"),
        }
        try: family,theorem=family_theorem[sig]
        except KeyError as exc: raise RelationCompositionError(f"unsupported BW_matmul relation signature: {sig}") from exc
        output=RelationFactSpec(layout,tuple(frontier),gather_dim=out_dim)
        certs.append(KRankBWMatmulCertificate(
            rule_id=f"bw-matmul-{family}-rank4",family=family,projection=sm.output_projection,
            rank_count=4,input_facts=tuple(facts),output_fact=output,sm_step_id=sm.step_id,
            pm_step_ids=tuple(x.step_id for x in pms),lean_theorem=theorem))
        rewritten.extend(input_frontiers);rewritten_layouts.extend(x[0] for x in relations)
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWLinearDwColumnShardedCertificate:
    rule_id: str
    rank_count: int
    gradient_fact: RelationFactSpec
    activation_fact: RelationFactSpec
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_linear_dw_column_sharded_frontiers(plan, ir, frontiers, layouts):
    """Input-column dW: shared g; ordered dim-2 x and dim-1 w/output shards."""
    import re
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("BW_linear dW frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        def keep():
            rewritten.append(frontier);rewritten_layouts.append(layout)
        if layout!="sharded" or len(frontier)<2 or not all(ref in by_id for ref in frontier):
            keep();continue
        sm,*pms=[by_id[ref] for ref in frontier];k=len(pms)
        if not (sm.side=="sm" and sm.op=="BW_linear" and sm.output_projection==".2"
                and all(p.side=="pm" and p.op==sm.op and p.output_projection==".2" for p in pms)):
            keep();continue
        if any(len(s.input_shapes)!=3 or len(s.input_bindings)!=3 for s in (sm,*pms)):
            raise RelationCompositionError("BW_linear dW column input arity mismatch")
        gfull,xfull,wfull=sm.input_shapes;outfull=sm.output_shape
        if not (len(gfull)==len(xfull)==3 and len(wfull)==len(outfull)==2
                and gfull[:2]==xfull[:2]==(1,8)):
            keep();continue
        # Axis provenance distinguishes this family even when K=1 and shapes coincide.
        refs=(sm.input_bindings[2],*(p.input_bindings[2] for p in pms))
        if not all(re.fullmatch(r"init:[0-9]+",r) for r in refs):
            keep();continue
        goal=ir.init_lineages.get(int(refs[0][5:]))
        if goal is None or goal.gatherDim!=1:
            keep();continue
        o,full_i=wfull
        if (type(o) is not int or type(full_i) is not int or o<=0 or full_i<=0
                or full_i%k or outfull!=wfull or gfull!=(1,8,o)
                or xfull!=(1,8,full_i)):
            raise RelationCompositionError("BW_linear dW column full shape mismatch")
        d=full_i//k;shard=(o,d)
        if any(p.input_shapes!=(gfull,(1,8,d),shard) or p.output_shape!=shard for p in pms):
            raise RelationCompositionError("BW_linear dW column local shape mismatch")
        if sm.rank!=0 or tuple(p.rank for p in pms)!=tuple(range(k)) or any(s.parameters for s in (sm,*pms)):
            raise RelationCompositionError("BW_linear dW column rank/parameter mismatch")
        if len({p.input_bindings[0] for p in pms})!=1:
            raise RelationCompositionError("BW_linear dW column gradient is not shared")
        if tuple(goal.tsShape)!=wfull or tuple(tuple(s) for s in goal.tpShapes)!=(shard,)*k:
            raise RelationCompositionError("BW_linear dW column weight lineage shape mismatch")
        weight=init_lineage_relation_fact(goal)
        if weight.layout!="sharded" or weight.step_triple!=refs or weight.gather_dim!=1:
            raise RelationCompositionError("BW_linear dW column weight lineage mismatch")
        grad=RelationFactSpec("joined",(sm.input_bindings[0],),joined_pm_step=pms[0].input_bindings[0])
        act=RelationFactSpec("sharded",(sm.input_bindings[1],*(p.input_bindings[1] for p in pms)),gather_dim=2)
        output=RelationFactSpec("sharded",frontier,gather_dim=1)
        certs.append(KRankBWLinearDwColumnShardedCertificate(
            rule_id="bw-linear-dw-input-column-sharded-k-rank",rank_count=k,
            gradient_fact=grad,activation_fact=act,weight_fact=weight,output_fact=output,
            sm_step_id=sm.step_id,pm_step_ids=tuple(p.step_id for p in pms),
            lean_theorem="TrainVerify.Denote.bw_linear_dw_input_allGatherPrimDimN_dim2_rank3"))
        rewritten.extend(((*grad.step_triple,grad.joined_pm_step),act.step_triple,weight.step_triple));rewritten_layouts.extend(("joined","sharded","sharded"))
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWLinearDwShardedCertificate:
    rule_id: str
    rank_count: int
    gradient_fact: RelationFactSpec
    activation_fact: RelationFactSpec
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_linear_dw_sharded_frontiers(plan, ir, frontiers, layouts):
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("BW_linear dW sharded frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="sharded" or len(frontier)!=5:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_linear" or sm.output_projection!=".2" or sm.side!="sm" or any(
            x.op!="BW_linear" or x.output_projection!=".2" or x.side!="pm" for x in pms
        ):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if tuple(int(x.rank) for x in pms)!=(0,1,2,3) or len(sm.input_bindings)!=3 or any(len(x.input_bindings)!=3 for x in pms):
            raise RelationCompositionError("rank-4 BW_linear dW sharded authority mismatch")
        gfull,xfull,wfull=map(tuple,sm.input_shapes);outfull=tuple(sm.output_shape)
        gshards=tuple(tuple(x.input_shapes[0]) for x in pms)
        xshards=tuple(tuple(x.input_shapes[1]) for x in pms)
        wshards=tuple(tuple(x.input_shapes[2]) for x in pms)
        outshards=tuple(tuple(x.output_shape) for x in pms)
        if (gfull[:2]!=(1,8) or xfull[:2]!=(1,8) or wfull!=outfull
                or len(gfull)!=3 or len(xfull)!=3 or len(wfull)!=2):
            raise RelationCompositionError("BW_linear dW full shapes are malformed")
        output_rows,input_cols=outfull
        expected_g=(1,8,output_rows//4);expected_w=(output_rows//4,input_cols)
        if (output_rows%4 or any(x!=expected_g for x in gshards)
                or any(x!=xfull for x in xshards)
                or any(x!=expected_w for x in wshards)
                or any(x!=expected_w for x in outshards)):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        grefs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        gradient_fact=RelationFactSpec("sharded",grefs,gather_dim=2)
        xrefs=tuple(x.input_bindings[1] for x in pms)
        if len(set(xrefs))!=1:
            raise RelationCompositionError("BW_linear dW activation is not joined/shared")
        activation_fact=RelationFactSpec("joined",(sm.input_bindings[1],),joined_pm_step=xrefs[0])
        activation_frontier=(sm.input_bindings[1],xrefs[0])
        weight_ref=sm.input_bindings[2];weight_refs=tuple(x.input_bindings[2] for x in pms)
        if not weight_ref.startswith("init:") or any(not x.startswith("init:") for x in weight_refs):
            raise RelationCompositionError("BW_linear dW sharded weight is not initial authority")
        weight_tid=int(weight_ref.split(":",1)[1])
        try: weight_fact=init_lineage_relation_fact(ir.init_lineages[weight_tid])
        except KeyError as exc: raise RelationCompositionError("BW_linear dW sharded weight InitGoal is missing") from exc
        if weight_fact.step_triple!=(weight_ref,*weight_refs) or weight_fact.gather_dim!=0:
            raise RelationCompositionError("BW_linear dW weight is not exact ordered dim-0 authority")
        theorem_by_shape={
            (32,32): "TrainVerify.Denote.bw_linear_dw_split_dim2_4_g119",
            (128,32): "TrainVerify.Denote.bw_linear_dw_col_split_dim2_4_1_8_32_g141",
            (32,128): "TrainVerify.Denote.bw_linear_dw_osplit_dim2_4_1_8_8_g179",
        }
        try: theorem=theorem_by_shape[outfull]
        except KeyError as exc: raise RelationCompositionError("BW_linear dW row sharding lacks checked theorem shape") from exc
        output=RelationFactSpec("sharded",tuple(frontier),gather_dim=0)
        certs.append(KRankBWLinearDwShardedCertificate(
            rule_id="bw-linear-dw-output-row-sharded-rank4",rank_count=4,
            gradient_fact=gradient_fact,activation_fact=activation_fact,
            weight_fact=weight_fact,output_fact=output,sm_step_id=sm.step_id,
            pm_step_ids=tuple(x.step_id for x in pms),lean_theorem=theorem))
        rewritten.extend((grefs,activation_frontier,weight_fact.step_triple))
        rewritten_layouts.extend(("sharded","joined",weight_fact.layout))
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWLinearDwReductionCertificate:
    rule_id: str
    rank_count: int
    shard_dim: int
    gradient_fact: RelationFactSpec
    activation_fact: RelationFactSpec
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_linear_dw_reduction_frontiers(plan, ir, frontiers, layouts):
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("BW_linear dW reduction frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="reduction" or len(frontier)!=5:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_linear" or sm.output_projection!=".2" or sm.side!="sm" or any(
            x.op!="BW_linear" or x.output_projection!=".2" or x.side!="pm" for x in pms
        ):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if tuple(int(x.rank) for x in pms)!=(0,1,2,3) or len(sm.input_bindings)!=3 or any(len(x.input_bindings)!=3 for x in pms):
            raise RelationCompositionError("rank-4 BW_linear dW writer/input authority mismatch")
        gfull,xfull,wfull=map(tuple,sm.input_shapes);outfull=tuple(sm.output_shape)
        if (len(gfull)!=3 or len(xfull)!=3 or len(wfull)!=2 or gfull[:2]!=(1,8)
                or xfull[:2]!=(1,8) or wfull!=outfull
                or wfull!=(gfull[2],xfull[2])):
            raise RelationCompositionError("BW_linear dW SM sequence shapes are malformed")
        expected_pm=((1,2,gfull[2]),(1,2,xfull[2]),wfull)
        if any(tuple(x.input_shapes)!=expected_pm or tuple(x.output_shape)!=outfull for x in pms):
            raise RelationCompositionError("BW_linear dW PM sequence shapes disagree")
        grefs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        xrefs=(sm.input_bindings[1],*(x.input_bindings[1] for x in pms))
        gradient_fact=RelationFactSpec("sharded",grefs,gather_dim=1)
        activation_fact=RelationFactSpec("sharded",xrefs,gather_dim=1)
        weight_ref=sm.input_bindings[2]
        if not weight_ref.startswith("init:") or any(x.input_bindings[2]!=weight_ref for x in pms):
            raise RelationCompositionError("BW_linear dW weight is not shared InitGoal authority")
        weight_tid=int(weight_ref.split(":",1)[1])
        try: weight_fact=init_lineage_relation_fact(ir.init_lineages[weight_tid])
        except KeyError as exc: raise RelationCompositionError("BW_linear dW weight InitGoal is missing") from exc
        if weight_fact.step_triple!=(weight_ref,weight_ref):
            raise RelationCompositionError("BW_linear dW weight InitGoal is not singleton")
        theorem_by_shape={
            (32,32): "TrainVerify.Denote.bw_linear_dw_dp_split_dim1_4_1_2_32_g170",
            (32,128): "TrainVerify.Denote.bw_linear_dw_dp_chunk_both_dim1_4_1_8_32_128_g144",
        }
        try: theorem=theorem_by_shape[outfull]
        except KeyError as exc: raise RelationCompositionError("BW_linear dW sequence reduction lacks checked theorem shape") from exc
        output=RelationFactSpec("reduction",tuple(frontier))
        certs.append(KRankBWLinearDwReductionCertificate(
            rule_id="bw-linear-dw-sequence-reduction-rank4",rank_count=4,shard_dim=1,
            gradient_fact=gradient_fact,activation_fact=activation_fact,
            weight_fact=weight_fact,output_fact=output,sm_step_id=sm.step_id,
            pm_step_ids=tuple(x.step_id for x in pms),lean_theorem=theorem))
        rewritten.extend((grefs,xrefs,weight_fact.step_triple))
        rewritten_layouts.extend(("sharded","sharded",weight_fact.layout))
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWLinearDxCertificate:
    rule_id: str
    family: str
    rank_count: int
    output_layout: str
    gather_dim: int | None
    input_facts: tuple[RelationFactSpec, ...]
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_linear_dx_frontiers(plan, ir, frontiers, layouts):
    """Classify checked GPT BW_linear dX relation transports."""
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("K-rank BW_linear dX frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    def initial_fact(sm_ref, pm_refs, expected_dim=None):
        if not sm_ref.startswith("init:") or any(not x.startswith("init:") for x in pm_refs):
            raise RelationCompositionError("BW_linear dX weight authority is not initial")
        tid=int(sm_ref.split(":",1)[1]);lineage=ir.init_lineages.get(tid)
        if lineage is None: raise RelationCompositionError(f"BW_linear dX missing InitGoal {tid}")
        fact=init_lineage_relation_fact(lineage)
        expected=((sm_ref,sm_ref) if len(set((sm_ref,*pm_refs)))==1 else (sm_ref,*pm_refs))
        if fact.step_triple!=expected:
            raise RelationCompositionError("BW_linear dX InitGoal refs do not match graph bindings")
        if expected_dim is not None and fact.gather_dim!=expected_dim:
            raise RelationCompositionError("BW_linear dX weight gather axis disagrees with InitGoal")
        return fact
    def joined(sm_ref, pm_refs):
        if len(set(pm_refs))!=1:
            raise RelationCompositionError("BW_linear dX shared PM input has distinct writers")
        return RelationFactSpec("joined",(sm_ref,),joined_pm_step=pm_refs[0]),(sm_ref,pm_refs[0]),"joined"
    for frontier,layout in zip(frontiers,layouts):
        if layout not in ("sharded","reduction") or len(frontier)<2:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_linear" or sm.side!="sm" or any(x.op!="BW_linear" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.output_projection!=".1" or any(x.output_projection!=".1" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        k=len(pms)
        if (sm.rank!=0 or sm.parameters or any(x.parameters for x in pms)
                or tuple(int(x.rank) for x in pms)!=tuple(range(k))
                or len(sm.input_bindings)!=3 or len(sm.input_shapes)!=3
                or any(len(x.input_bindings)!=3 or len(x.input_shapes)!=3 for x in pms)):
            raise RelationCompositionError("K-rank BW_linear dX writer/input authority mismatch")
        grefs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        xrefs=(sm.input_bindings[1],*(x.input_bindings[1] for x in pms))
        wsm=sm.input_bindings[2];wpms=tuple(x.input_bindings[2] for x in pms)
        full_out=tuple(sm.output_shape);piece_out=tuple(pms[0].output_shape)
        pm_g=tuple(tuple(x.input_shapes[0]) for x in pms)
        pm_x=tuple(tuple(x.input_shapes[1]) for x in pms)
        pm_w=tuple(tuple(x.input_shapes[2]) for x in pms)
        if any(tuple(x.output_shape)!=piece_out for x in pms) or any(s!=pm_g[0] for s in pm_g) or any(s!=pm_x[0] for s in pm_x) or any(s!=pm_w[0] for s in pm_w):
            raise RelationCompositionError("BW_linear dX PM shapes disagree across ranks")
        input_facts=[];input_frontiers=[];input_layouts=[]
        if layout=="sharded" and full_out[:2]==(1,8) and piece_out[:2]==(1,2) and full_out[2]==piece_out[2] and pm_g[0]==(1,2,32) and pm_w[0]==tuple(sm.input_shapes[2]):
            if k != 4:
                raise RelationCompositionError("sequence-sharded BW_linear dX remains rank-4")
            family="sequence-sharded";dim=1
            input_facts=[RelationFactSpec("sharded",grefs,gather_dim=1),RelationFactSpec("sharded",xrefs,gather_dim=1),initial_fact(wsm,wpms)]
            input_frontiers=[x.step_triple for x in input_facts];input_layouts=[x.layout for x in input_facts]
            theorem=("TrainVerify.Denote.bw_linear_dx_dp_split_dim1_4_g169" if full_out[2]==32
                     else "TrainVerify.Denote.bw_linear_dx_dp_split_dim1_4_g143")
        elif (layout=="sharded" and len(piece_out)==3 and piece_out[:2]==(1,8)
                and len(pm_g[0])==3 and pm_g[0][:2]==(1,8)
                and piece_out[2]>0 and pm_g[0][2]>0
                and full_out==(1,8,piece_out[2]*k)
                and tuple(sm.input_shapes[0])==pm_g[0]
                and tuple(sm.input_shapes[1])==full_out and pm_x[0]==piece_out
                and tuple(sm.input_shapes[2])==(pm_g[0][2],piece_out[2]*k)
                and pm_w[0]==(pm_g[0][2],piece_out[2])):
            family="column-sharded";dim=2
            gfact,gfront,glayout=joined(grefs[0],grefs[1:])
            xfact=RelationFactSpec("sharded",xrefs,gather_dim=2)
            wfact=initial_fact(wsm,wpms,expected_dim=1)
            lineage=ir.init_lineages[int(wsm.split(":",1)[1])]
            if (tuple(lineage.tsShape)!=tuple(sm.input_shapes[2])
                    or tuple(tuple(s) for s in lineage.tpShapes)!=pm_w
                    or tuple(r for r,_ in lineage.tps)!=tuple(range(k))):
                raise RelationCompositionError("BW_linear column dX weight lineage shape/rank mismatch")
            input_facts=[gfact,xfact,wfact]
            input_frontiers=[gfront,xfact.step_triple,wfact.step_triple]
            input_layouts=[glayout,"sharded",wfact.layout]
            theorem="TrainVerify.Denote.bw_linear_dx_weight_allGatherPrimDimN_dim1_rank3"
        elif (layout=="reduction" and len(full_out)==3 and len(piece_out)==3
                and len(tuple(sm.input_shapes[0]))==3 and len(pm_g[0])==3
                and len(tuple(sm.input_shapes[1]))==3
                and len(tuple(sm.input_shapes[2]))==2 and len(pm_w[0])==2
                and piece_out==full_out==tuple(sm.input_shapes[1])
                and tuple(sm.input_shapes[0])[:2]==pm_g[0][:2]==full_out[:2]
                and tuple(sm.input_shapes[0])[2]==pm_g[0][2]*k
                and tuple(sm.input_shapes[2])==(tuple(sm.input_shapes[0])[2],full_out[2])
                and pm_w[0]==(pm_g[0][2],full_out[2])
                and all(x>0 for x in (*full_out,pm_g[0][2]))):
            family="row-reduction";dim=None
            gfact=RelationFactSpec("sharded",grefs,gather_dim=2)
            xfact,xfront,xlayout=joined(xrefs[0],xrefs[1:])
            wfact=initial_fact(wsm,wpms,expected_dim=0)
            input_facts=[gfact,xfact,wfact];input_frontiers=[gfact.step_triple,xfront,wfact.step_triple];input_layouts=["sharded",xlayout,wfact.layout]
            dynamic_key=(pm_g[0],tuple(sm.input_shapes[1]),pm_w[0])
            if dynamic_key==((1,8,32),(1,8,32),(32,32)):
                theorem="TrainVerify.Denote.bw_linear_dx_allGatherPrimDimN_dim2_rank3"
            elif k==4:
                theorem_by_shapes = {
                    ((1,8,8),(1,8,32),(8,32)):
                        "TrainVerify.Denote.bw_linear_dx_tp_split_dim2_4_g134",
                    ((1,8,8),(1,8,128),(8,128)):
                        "TrainVerify.Denote.bw_linear_dx_tp_split_dim2_4_g178",
                }
                try: theorem=theorem_by_shapes[dynamic_key]
                except KeyError as exc:
                    raise RelationCompositionError(
                        "BW_linear row-reduction dX is outside checked theorem shapes"
                    ) from exc
            else:
                raise RelationCompositionError(
                    "dynamic-K BW_linear row-reduction is only checked for 32-wide dX"
                )
        else:
            raise RelationCompositionError(
                f"unsupported BW_linear dX relation topology: layout={layout}, output={full_out}/{piece_out}, g={tuple(sm.input_shapes[0])}/{pm_g[0]}, w={tuple(sm.input_shapes[2])}/{pm_w[0]}"
            )
        output=RelationFactSpec(layout,tuple(frontier),gather_dim=dim)
        rule_id=("bw-linear-dx-row-reduction-k-rank"
                 if theorem=="TrainVerify.Denote.bw_linear_dx_allGatherPrimDimN_dim2_rank3"
                 else "bw-linear-dx-column-sharded-k-rank"
                 if theorem=="TrainVerify.Denote.bw_linear_dx_weight_allGatherPrimDimN_dim1_rank3"
                 else f"bw-linear-dx-{family}-rank4")
        certs.append(KRankBWLinearDxCertificate(
            rule_id=rule_id,family=family,rank_count=k,
            output_layout=layout,gather_dim=dim,input_facts=tuple(input_facts),output_fact=output,
            sm_step_id=sm.step_id,pm_step_ids=tuple(x.step_id for x in pms),lean_theorem=theorem))
        rewritten.extend(input_frontiers);rewritten_layouts.extend(input_layouts)
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWLayernormParamReductionCertificate:
    rule_id: str
    projection: str
    rank_count: int
    gradient_fact: RelationFactSpec
    activation_fact: RelationFactSpec
    gamma_fact: RelationFactSpec
    beta_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_layernorm_param_reduction_frontiers(plan, ir, frontiers, layouts):
    if len(frontiers)!=len(layouts):
        raise RelationCompositionError("BW_layernorm parameter reduction frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="reduction" or len(frontier)!=5:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_layernorm" or sm.side!="sm" or any(x.op!="BW_layernorm" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        projection=sm.output_projection
        if projection not in (".2.1", ".2.2") or any(x.output_projection!=projection for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if tuple(int(x.rank) for x in pms)!=(0,1,2,3) or len(sm.input_bindings)!=4 or any(len(x.input_bindings)!=4 for x in pms):
            raise RelationCompositionError("rank-4 BW_layernorm parameter writer/input authority mismatch")
        if tuple(sm.input_shapes)!=((1,8,32),(1,8,32),(32,),(32,)) or tuple(sm.output_shape)!=(32,):
            raise RelationCompositionError("BW_layernorm parameter SM is outside checked theorem shapes")
        if any(tuple(x.input_shapes)!=((1,2,32),(1,2,32),(32,),(32,)) or tuple(x.output_shape)!=(32,) for x in pms):
            raise RelationCompositionError("BW_layernorm parameter PM is outside checked theorem shapes")
        grefs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        xrefs=(sm.input_bindings[1],*(x.input_bindings[1] for x in pms))
        gradient_fact=RelationFactSpec("sharded",grefs,gather_dim=1)
        activation_fact=RelationFactSpec("sharded",xrefs,gather_dim=1)
        shared=[]
        for argument in (2,3):
            ref=sm.input_bindings[argument]
            if not ref.startswith("init:") or any(x.input_bindings[argument]!=ref for x in pms):
                raise RelationCompositionError("BW_layernorm parameter is not shared InitGoal authority")
            tid=int(ref.split(":",1)[1])
            try: fact=init_lineage_relation_fact(ir.init_lineages[tid])
            except KeyError as exc: raise RelationCompositionError("BW_layernorm parameter InitGoal is missing") from exc
            if fact.step_triple!=(ref,ref):
                raise RelationCompositionError("BW_layernorm parameter InitGoal is not singleton")
            shared.append(fact)
        output=RelationFactSpec("reduction",tuple(frontier))
        certs.append(KRankBWLayernormParamReductionCertificate(
            rule_id=("bw-layernorm-dgamma-reduction-rank4" if projection==".2.1"
                     else "bw-layernorm-dbeta-reduction-rank4"),
            projection=projection,rank_count=4,
            gradient_fact=gradient_fact,activation_fact=activation_fact,
            gamma_fact=shared[0],beta_fact=shared[1],output_fact=output,
            sm_step_id=sm.step_id,pm_step_ids=tuple(x.step_id for x in pms),
            lean_theorem=("TrainVerify.Denote.bw_layernorm_dw_dp_split_dim1_4_1_2_32"
                          if projection==".2.1" else
                          "TrainVerify.Denote.bw_layernorm_db_dp_split_dim1_4_1_2_32")))
        rewritten.extend((grefs,xrefs,shared[0].step_triple,shared[1].step_triple))
        rewritten_layouts.extend(("sharded","sharded",shared[0].layout,shared[1].layout))
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWLayernormDxCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    gradient_fact: RelationFactSpec
    activation_fact: RelationFactSpec
    gamma_fact: RelationFactSpec
    beta_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str
    full_shape: tuple[int, ...] = ()
    shard_shape: tuple[int, ...] = ()


def advance_k_rank_bw_layernorm_dx_frontiers(plan, ir, frontiers, layouts):
    """Transport last-axis LayerNorm dX through an ordered dim-1 gather."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank BW_layernorm frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="sharded" or len(frontier)<2:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_layernorm" or sm.side!="sm" or any(x.op!="BW_layernorm" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.output_projection != ".1" or any(x.output_projection != ".1" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        k = len(pms)
        if (sm.rank != 0 or sm.parameters or any(x.parameters for x in pms)
                or tuple(x.rank for x in pms) != tuple(range(k))
                or len(sm.input_bindings) != 4 or len(sm.input_shapes) != 4
                or any(len(x.input_bindings) != 4 or len(x.input_shapes) != 4 for x in pms)):
            raise RelationCompositionError("K-rank BW_layernorm dx writer/input authority mismatch")
        full, shard = tuple(sm.output_shape), tuple(pms[0].output_shape)
        if (len(full) != 3 or len(shard) != 3 or any(d <= 0 for d in shard)
                or full != (shard[0], shard[1] * k, shard[2])):
            raise RelationCompositionError("BW_layernorm dx dim-1 shape contract mismatch")
        d = shard[2]
        if (tuple(sm.input_shapes) != (full, full, (d,), (d,))
                or any(tuple(x.output_shape) != shard
                       or tuple(x.input_shapes) != (shard, shard, (d,), (d,)) for x in pms)):
            raise RelationCompositionError("BW_layernorm dx input shapes violate the theorem domain")
        gradient_refs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        activation_refs=(sm.input_bindings[1],*(x.input_bindings[1] for x in pms))
        shared=[]
        for argument,label in ((2,"gamma"),(3,"beta")):
            refs=(sm.input_bindings[argument],*(x.input_bindings[argument] for x in pms))
            if len(set(refs))!=1 or not refs[0].startswith("init:"):
                raise RelationCompositionError(f"BW_layernorm dx {label} is not one shared init authority")
            tid=int(refs[0].split(":",1)[1]);lineage=ir.init_lineages.get(tid)
            if lineage is None:
                raise RelationCompositionError(f"BW_layernorm dx {label} InitGoal is missing")
            fact=init_lineage_relation_fact(lineage)
            if (len(lineage.tps)!=1 or fact.step_triple!=(refs[0],refs[0])
                    or tuple(lineage.tsShape)!=(d,) or tuple(map(tuple,lineage.tpShapes))!=((d,),)):
                raise RelationCompositionError(f"BW_layernorm dx {label} is not singleton public authority")
            shared.append(fact)
        gradient_fact=RelationFactSpec("sharded",gradient_refs,gather_dim=1)
        activation_fact=RelationFactSpec("sharded",activation_refs,gather_dim=1)
        output_fact=RelationFactSpec("sharded",tuple(frontier),gather_dim=1)
        certs.append(KRankBWLayernormDxCertificate(
            rule_id="bw-layernorm-dx-dim1-k-rank",rank_count=k,gather_dim=1,
            gradient_fact=gradient_fact,activation_fact=activation_fact,
            gamma_fact=shared[0],beta_fact=shared[1],output_fact=output_fact,
            sm_step_id=sm.step_id,pm_step_ids=tuple(x.step_id for x in pms),
            lean_theorem="TrainVerify.Denote.bw_layernorm_dx_allGatherPrimDimN_dim1_3d",
            full_shape=full, shard_shape=shard))
        rewritten.extend((gradient_refs,activation_refs,shared[0].step_triple,shared[1].step_triple))
        rewritten_layouts.extend(("sharded","sharded",shared[0].layout,shared[1].layout))
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWMultirefSumCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    input_facts: tuple[RelationFactSpec, ...]
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str
    full_shape: tuple[int, ...] = ()
    shard_shape: tuple[int, ...] = ()


def advance_k_rank_bw_multiref_sum_frontiers(plan, frontiers, layouts):
    if len(frontiers)!=len(layouts): raise RelationCompositionError("K-rank BW_multiref frontier/layout arity mismatch")
    by_id={s.step_id:s for s in plan.steps};certs=[];rewritten=[];rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="sharded" or len(frontier)<2:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try: sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_multiref" or sm.side!="sm" or any(x.op!="BW_multiref" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        k=len(pms);arity=len(sm.input_bindings)
        if sm.rank!=0 or any(x.parameters or x.output_projection for x in (sm,*pms)):
            raise RelationCompositionError("K-rank BW_multiref writer rank/params/projection mismatch")
        if arity<=0 or any(len(x.input_bindings)!=arity for x in pms) or tuple(int(x.rank) for x in pms)!=tuple(range(k)):
            raise RelationCompositionError("K-rank BW_multiref input/rank arity mismatch")
        full=tuple(sm.output_shape);shards=tuple(tuple(x.output_shape) for x in pms);shard=shards[0]
        if len(full)!=3 or any(len(x)!=3 or any(type(d) is not int or d<=0 for d in x) for x in (full,*shards)):
            raise RelationCompositionError("K-rank BW_multiref requires positive rank3 shapes")
        candidates=[d for d in range(len(full)) if full[d]==shard[d]*k and all(full[i]==shard[i] for i in range(len(full)) if i!=d)]
        if any(x!=shard for x in shards) or len(candidates)!=1:
            raise RelationCompositionError("K-rank BW_multiref output sharding is ambiguous")
        dim=candidates[0];inputs=[]
        if dim not in (1,2):
            raise RelationCompositionError("K-rank BW_multiref requires dim1/dim2 authority")
        for arg in range(arity):
            refs=(sm.input_bindings[arg],*(x.input_bindings[arg] for x in pms))
            try: steps=(by_id[refs[0]],*(by_id[x] for x in refs[1:]))
            except KeyError as exc: raise RelationCompositionError("K-rank BW_multiref input writer unresolved") from exc
            if steps[0].side!="sm" or steps[0].rank!=0 or any(x.side!="pm" or x.rank!=r for r,x in enumerate(steps[1:])):
                raise RelationCompositionError("K-rank BW_multiref input writer rank order mismatch")
            if tuple(steps[0].output_shape)!=full or any(tuple(x.output_shape)!=shard for x in steps[1:]):
                raise RelationCompositionError("K-rank BW_multiref input shapes disagree with output sharding")
            inputs.append(RelationFactSpec("sharded",refs,gather_dim=dim))
        output=RelationFactSpec("sharded",tuple(frontier),gather_dim=dim)
        lean_theorem = "TrainVerify.Denote.tensorSum_allGather_dim_K"
        certs.append(KRankBWMultirefSumCertificate(
            rule_id="bw-multiref-sum-sharded-k-rank",rank_count=k,gather_dim=dim,
            input_facts=tuple(inputs),output_fact=output,sm_step_id=sm.step_id,
            pm_step_ids=tuple(x.step_id for x in pms),lean_theorem=lean_theorem,
            full_shape=full,shard_shape=shard))
        rewritten.extend(x.step_triple for x in inputs);rewritten_layouts.extend("sharded" for _ in inputs)
    return tuple(certs),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankBWAddIdentityCertificate:
    rule_id: str
    rank_count: int
    gather_dim: int
    projection: str
    input_fact: RelationFactSpec
    operand_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_bw_add_identity_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankBWAddIdentityCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Propagate same-shape BW_add projections through the upstream gradient."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank BW_add frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates=[]; rewritten=[]; rewritten_layouts=[]
    for frontier,layout in zip(frontiers,layouts):
        if layout!="sharded" or len(frontier)<2:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        try:
            sm=by_id[frontier[0]];pms=tuple(by_id[x] for x in frontier[1:])
        except KeyError:
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        if sm.op!="BW_add" or sm.side!="sm" or any(x.op!="BW_add" or x.side!="pm" for x in pms):
            rewritten.append(frontier);rewritten_layouts.append(layout);continue
        projection=sm.output_projection
        if projection not in (".1",".2") or any(x.output_projection!=projection for x in pms):
            raise RelationCompositionError("K-rank BW_add projection authority mismatch")
        k=len(pms)
        if tuple(int(x.rank) for x in pms)!=tuple(range(k)) or len(sm.input_bindings)!=3 or any(len(x.input_bindings)!=3 for x in pms):
            raise RelationCompositionError("K-rank BW_add writer/rank arity mismatch")
        operand=1 if projection==".1" else 2
        if tuple(sm.input_shapes[0])!=tuple(sm.input_shapes[operand]) or any(
            tuple(x.input_shapes[0])!=tuple(x.input_shapes[operand]) for x in pms
        ):
            raise RelationCompositionError("K-rank BW_add projection is not same-shape identity")
        input_refs=(sm.input_bindings[0],*(x.input_bindings[0] for x in pms))
        operand_refs=(sm.input_bindings[operand],*(x.input_bindings[operand] for x in pms))
        full=tuple(sm.output_shape);shards=tuple(tuple(x.output_shape) for x in pms)
        if not shards or any(x!=shards[0] for x in shards):
            raise RelationCompositionError("K-rank BW_add output shard shapes disagree")
        shard=shards[0]
        candidates=[d for d in range(len(full)) if full[d]==shard[d]*k and all(full[i]==shard[i] for i in range(len(full)) if i!=d)]
        if len(candidates)!=1:
            raise RelationCompositionError(f"K-rank BW_add output does not determine one axis: {candidates}")
        dim=candidates[0]
        input_fact=RelationFactSpec("sharded",input_refs,gather_dim=dim)
        operand_fact=RelationFactSpec("sharded",operand_refs,gather_dim=dim)
        output_fact=RelationFactSpec("sharded",tuple(frontier),gather_dim=dim)
        certificates.append(KRankBWAddIdentityCertificate(
            rule_id="bw-add-identity-sharded-k-rank",rank_count=k,gather_dim=dim,
            projection=projection,input_fact=input_fact,operand_fact=operand_fact,
            output_fact=output_fact,
            sm_step_id=sm.step_id,pm_step_ids=tuple(x.step_id for x in pms),
            lean_theorem=("TrainVerify.Denote.bw_add2_fst_same_shape"
                          if projection==".1" else
                          "TrainVerify.Denote.bw_add2_snd_same_shape")))
        rewritten.extend((input_refs,operand_refs));rewritten_layouts.extend(("sharded","sharded"))
    return tuple(certificates),tuple(rewritten),tuple(rewritten_layouts)


@dataclass(frozen=True)
class KRankAllToAllRelationCertificate:
    rule_id: str
    rank_count: int
    input_gather_dim: int
    output_gather_dim: int
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    pm_step_ids: tuple[str, ...]
    lean_theorem: str


def advance_k_rank_alltoall_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[KRankAllToAllRelationCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Peel one rank-count-polymorphic AllToAll layout transport.

    A sharded full tensor reconstructed along ``idim`` is unchanged globally;
    the K rank-local AllToAll writers only change its reconstruction dimension
    to ``odim``.  Rank order and every declared shape are authority.
    """

    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank AllToAll frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "sharded":
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if len(frontier) < 2:
            raise RelationCompositionError("K-rank AllToAll frontier has no PM ranks")
        if any(ref.startswith("init:") for ref in frontier):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        sm_ref, *pm_output_refs = frontier
        rank_count = len(pm_output_refs)
        sm_step = by_id.get(sm_ref)
        pm_steps = tuple(by_id.get(ref) for ref in pm_output_refs)
        if sm_step is None or sm_step.side != "sm" or any(step is None for step in pm_steps):
            raise RelationCompositionError("K-rank AllToAll frontier contains unknown or wrong-side steps")
        if any(step.side != "pm" or step.op != "AllToAllPrim" for step in pm_steps):
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if tuple(step.rank for step in pm_steps) != tuple(range(rank_count)):
            raise RelationCompositionError("K-rank AllToAll writers are not in exact rank order")
        parameter_sets = {step.parameters for step in pm_steps}
        if len(parameter_sets) != 1:
            raise RelationCompositionError("K-rank AllToAll writers disagree on dimensions")
        params = next(iter(parameter_sets))
        if len(params) != 2:
            raise RelationCompositionError("K-rank AllToAll requires exactly input/output dimensions")
        input_dim, output_dim = params
        input_bindings = pm_steps[0].input_bindings
        if len(input_bindings) != rank_count or any(
            step.input_bindings != input_bindings for step in pm_steps[1:]
        ):
            raise RelationCompositionError("K-rank AllToAll writers do not share one ordered input list")
        input_steps = tuple(by_id.get(ref) for ref in input_bindings)
        if any(step is None or step.side != "pm" for step in input_steps):
            raise RelationCompositionError("K-rank AllToAll input list has unknown or wrong-side steps")
        input_shapes = tuple(step.output_shape for step in input_steps)
        output_shapes = tuple(step.output_shape for step in pm_steps)
        if len(set(input_shapes)) != 1 or len(set(output_shapes)) != 1:
            raise RelationCompositionError("K-rank AllToAll shard shapes disagree across ranks")
        full_shape = tuple(sm_step.output_shape)

        def gathered_shape(shard_shape: tuple[int, ...], dim: int) -> tuple[int, ...]:
            if dim < 0 or dim >= len(shard_shape):
                raise RelationCompositionError(f"K-rank AllToAll dimension is out of bounds: {dim}")
            result = list(shard_shape)
            result[dim] *= rank_count
            return tuple(result)

        if gathered_shape(input_shapes[0], input_dim) != full_shape:
            raise RelationCompositionError("K-rank AllToAll input shards do not reconstruct the SM tensor")
        if gathered_shape(output_shapes[0], output_dim) != full_shape:
            raise RelationCompositionError("K-rank AllToAll outputs do not reconstruct the SM tensor")
        input_fact = RelationFactSpec("sharded", (sm_ref, *input_bindings), gather_dim=input_dim)
        output_fact = RelationFactSpec("sharded", frontier, gather_dim=output_dim)
        certificates.append(KRankAllToAllRelationCertificate(
            rule_id="alltoall-k-rank-layout-transport",
            rank_count=rank_count,
            input_gather_dim=input_dim,
            output_gather_dim=output_dim,
            input_fact=input_fact,
            output_fact=output_fact,
            pm_step_ids=tuple(pm_output_refs),
            lean_theorem="TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn",
        ))
        rewritten.append(input_fact.step_triple)
        rewritten_layouts.append("sharded")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class JoinedInitMultirefCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    pm_step_id: str
    projection: int
    arity: int
    lean_theorem: str


def advance_joined_init_multiref_frontiers(plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("joined-init multiref frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "joined" or len(frontier) != 2 or not frontier[0].startswith("init:"):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        sm_ref, pm_ref = frontier
        pm_step = by_id.get(pm_ref)
        if pm_step is None or pm_step.side != "pm" or pm_step.op != "FW_multiref":
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if (len(pm_step.input_bindings) != 1 or len(pm_step.parameters) != 1
                or not 0 <= pm_step.output_index < pm_step.parameters[0]):
            raise RelationCompositionError("joined-init multiref signature is malformed")
        pm_input = pm_step.input_bindings[0]
        input_fact = RelationFactSpec("joined", (sm_ref,), joined_pm_step=pm_input)
        output_fact = RelationFactSpec("joined", (sm_ref,), joined_pm_step=pm_ref)
        certificates.append(JoinedInitMultirefCertificate(
            rule_id="joined-init-multiref-alias",
            input_fact=input_fact, output_fact=output_fact,
            pm_step_id=pm_ref, projection=pm_step.output_index,
            arity=pm_step.parameters[0],
            lean_theorem="TrainVerify.Denote.applyNode_fw_multiref_at",
        ))
        rewritten.append((sm_ref, pm_input)); rewritten_layouts.append("joined")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class JoinedInitMultirefGroupCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    output_facts: tuple[RelationFactSpec, ...]
    pm_step_ids: tuple[str, ...]
    projections: tuple[int, ...]
    arity: int
    lean_theorem: str


def group_joined_init_multiref_certificates(certificates):
    grouped = {}
    passthrough = []
    for certificate in certificates:
        if type(certificate) is not JoinedInitMultirefCertificate:
            passthrough.append(certificate)
            continue
        if certificate.rule_id != "joined-init-multiref-alias":
            raise RelationCompositionError("joined-init multiref has unexpected rule identity")
        if not 0 <= certificate.projection < certificate.arity:
            raise RelationCompositionError("joined-init multiref projection is out of range")
        try:
            step_projection = int(certificate.pm_step_id.rsplit(":", 1)[1])
        except (IndexError, ValueError) as exc:
            raise RelationCompositionError("joined-init multiref step projection is malformed") from exc
        if (step_projection != certificate.projection
                or certificate.output_fact.layout != "joined"
                or certificate.output_fact.step_triple != certificate.input_fact.step_triple
                or certificate.output_fact.joined_pm_step != certificate.pm_step_id):
            raise RelationCompositionError("joined-init multiref projection/fact identity disagrees")
        writer = certificate.pm_step_id.rsplit(":", 1)[0]
        key = (certificate.input_fact, writer, certificate.arity, certificate.lean_theorem)
        grouped.setdefault(key, []).append(certificate)
    result = list(passthrough)
    for (input_fact, _writer, arity, theorem), items in sorted(
        grouped.items(), key=lambda item: repr(item[0])
    ):
        ordered = tuple(sorted(items, key=lambda item: item.projection))
        projections = tuple(item.projection for item in ordered)
        if len(set(projections)) != len(projections):
            raise RelationCompositionError("joined-init multiref group has duplicate projection")
        if any(item.input_fact != input_fact or item.arity != arity
               or item.lean_theorem != theorem for item in ordered):
            raise RelationCompositionError("joined-init multiref group authority disagrees")
        output_facts = tuple(item.output_fact for item in ordered)
        if len(set(output_facts)) != len(output_facts):
            raise RelationCompositionError("joined-init multiref group has duplicate output fact")
        result.append(JoinedInitMultirefGroupCertificate(
            rule_id="joined-init-multiref-alias-group",
            input_fact=input_fact,
            output_facts=output_facts,
            pm_step_ids=tuple(item.pm_step_id for item in ordered),
            projections=projections,
            arity=arity,
            lean_theorem=theorem,
        ))
    return tuple(result)


@dataclass(frozen=True)
class JoinedZigzagAllGatherCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    pm_allgather_step: str
    lean_theorem: str


def advance_joined_zigzag_allgather_frontiers(plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("joined-zigzag frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "joined_zigzag" or len(frontier) != 2:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        sm_ref, joined_ref = frontier
        try:
            sm_step, joined = (by_id[ref] for ref in frontier)
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if joined.op != "AllGatherPrim":
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if (sm_step.side != "sm" or joined.side != "pm"
                or int(joined.rank) != 0 or tuple(joined.parameters) != (0,)
                or len(joined.input_bindings) != 2):
            raise RelationCompositionError("joined-zigzag AllGather authority mismatch")
        row0_ref, row1_ref = joined.input_bindings
        try:
            row0, row1 = by_id[row0_ref], by_id[row1_ref]
        except KeyError as exc:
            raise RelationCompositionError("joined-zigzag AllGather row source is unresolved") from exc
        if tuple(joined.output_shape) != tuple(sm_step.output_shape):
            raise RelationCompositionError("joined-zigzag full output shape mismatch")
        if tuple(row0.output_shape) != tuple(row1.output_shape):
            raise RelationCompositionError("joined-zigzag row shard shapes disagree")
        row_shape = tuple(row0.output_shape)
        if not row_shape or tuple(sm_step.output_shape) != (2 * row_shape[0], *row_shape[1:]):
            raise RelationCompositionError("joined-zigzag rows do not reconstruct full shape")
        input_fact = RelationFactSpec("zigzag", (sm_ref, row0_ref, row1_ref))
        output_fact = RelationFactSpec(
            "joined_zigzag", (sm_ref,), joined_pm_step=joined_ref
        )
        certificates.append(JoinedZigzagAllGatherCertificate(
            rule_id="zigzag-allgather-joined-two-rank",
            input_fact=input_fact,
            output_fact=output_fact,
            pm_allgather_step=joined_ref,
            lean_theorem="TrainVerify.Denote.RelationCompiler.JoinedZigzagRel.of_allGather",
        ))
        rewritten.append((sm_ref, row0_ref, row1_ref))
        rewritten_layouts.append("zigzag")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class ZigzagFeatureOutputLinearCertificate:
    rule_id: str
    activation_fact: RelationFactSpec
    weight_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_ids: tuple[str, str]
    rows: int
    input_features: int
    output_feature: int
    lean_theorem: str


def advance_zigzag_feature_output_linear_frontiers(ir, plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("zigzag-feature output-linear frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "zigzag_feature" or len(frontier) != 3 or any(ref.startswith("init:") for ref in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            sm_step, pm0, pm1 = (by_id[ref] for ref in frontier)
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if any(step.op != "FW_mix_precision_linear" for step in (sm_step, pm0, pm1)):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if (pm0.rank, pm1.rank) != (0, 1) or any(
            len(step.input_bindings) != 2 or len(step.input_shapes) != 2
            for step in (sm_step, pm0, pm1)
        ):
            raise RelationCompositionError("zigzag-feature output-linear writer authority is malformed")
        if pm0.input_bindings[0] != pm1.input_bindings[0]:
            raise RelationCompositionError("zigzag-feature output-linear PM activation is not one joined writer")
        sm_weight_ref = sm_step.input_bindings[1]
        pm_weight_refs = (pm0.input_bindings[1], pm1.input_bindings[1])
        if not sm_weight_ref.startswith("init:") or any(not ref.startswith("init:") for ref in pm_weight_refs):
            raise RelationCompositionError("zigzag-feature output-linear weights lack InitGoal authority")
        full_weight_tid = int(sm_weight_ref.split(":", 1)[1])
        lineage = ir.init_lineages.get(full_weight_tid)
        if lineage is None:
            raise RelationCompositionError("zigzag-feature output-linear weight lineage is missing")
        weight_fact = init_lineage_relation_fact(lineage)
        if (weight_fact.layout != "sharded" or weight_fact.gather_dim != 0
                or weight_fact.step_triple != (sm_weight_ref, *pm_weight_refs)):
            raise RelationCompositionError("zigzag-feature output-linear weight lineage/order mismatch")
        activation_shape = tuple(sm_step.input_shapes[0]); pm_activation_shape = tuple(pm0.input_shapes[0])
        full_weight_shape = tuple(sm_step.input_shapes[1]); shard_weight_shape = tuple(pm0.input_shapes[1])
        full_output = tuple(sm_step.output_shape); feature_output = tuple(pm0.output_shape)
        if (tuple(pm1.input_shapes[0]) != pm_activation_shape
                or tuple(pm1.input_shapes[1]) != shard_weight_shape
                or tuple(pm1.output_shape) != feature_output
                or len(activation_shape) != 2 or activation_shape != pm_activation_shape
                or full_weight_shape != (shard_weight_shape[0] * 2, shard_weight_shape[1])
                or activation_shape[1] != full_weight_shape[1]
                or full_output != (activation_shape[0], full_weight_shape[0])
                or full_output != (feature_output[0], feature_output[1] * 2)
                or activation_shape[0] % 2 != 0
                or min((*activation_shape, *shard_weight_shape, *feature_output)) <= 0):
            raise RelationCompositionError("zigzag-feature output-linear shape contract fails")
        activation_fact = RelationFactSpec(
            "joined_zigzag", (sm_step.input_bindings[0],),
            joined_pm_step=pm0.input_bindings[0]
        )
        output_fact = RelationFactSpec("zigzag_feature", tuple(frontier), gather_dim=1)
        certificates.append(ZigzagFeatureOutputLinearCertificate(
            rule_id="zigzag-feature-output-linear-two-rank",
            activation_fact=activation_fact, weight_fact=weight_fact,
            output_fact=output_fact, sm_step_id=sm_step.step_id,
            pm_step_ids=(pm0.step_id, pm1.step_id),
            rows=activation_shape[0] // 2,
            input_features=activation_shape[1], output_feature=feature_output[1],
            lean_theorem="TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.output_sharded_linear_two",
        ))
        rewritten.extend(((sm_step.input_bindings[0], pm0.input_bindings[0]), weight_fact.step_triple))
        rewritten_layouts.extend(("joined_zigzag", "sharded"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class ZigzagFeatureBinaryCertificate:
    rule_id: str
    input_facts: tuple[RelationFactSpec, RelationFactSpec]
    output_fact: RelationFactSpec
    writer_steps: tuple[str, str, str]
    rows: int
    input_features: int
    feature_features: int
    lean_theorem: str


def advance_zigzag_feature_binary_frontiers(plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("zigzag-feature binary frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "zigzag_feature" or len(frontier) != 3 or any(ref.startswith("init:") for ref in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            steps = tuple(by_id[ref] for ref in frontier)
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if any(step.op != "FW_swiglu" for step in steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if any(len(step.input_bindings) != 2 or len(step.input_shapes) != 2 for step in steps):
            raise RelationCompositionError("zigzag-feature SwiGLU signature mismatch")
        full_shape = tuple(steps[0].output_shape); feature_shape = tuple(steps[1].output_shape)
        if (tuple(steps[2].output_shape) != feature_shape or len(full_shape) != 2
                or len(feature_shape) != 2
                or full_shape != (feature_shape[0], feature_shape[1] * 2)
                or full_shape[0] % 2 != 0
                or min(feature_shape) <= 0):
            raise RelationCompositionError("zigzag-feature SwiGLU shape contract fails")
        inputs = tuple(_produced_binding_triple(steps, index) for index in range(2))
        input_facts = tuple(RelationFactSpec("zigzag_feature", refs, gather_dim=1) for refs in inputs)
        output_fact = RelationFactSpec("zigzag_feature", tuple(frontier), gather_dim=1)
        certificates.append(ZigzagFeatureBinaryCertificate(
            rule_id="zigzag-feature-swiglu-two-rank",
            input_facts=input_facts, output_fact=output_fact,
            writer_steps=tuple(frontier),
            rows=full_shape[0] // 2, input_features=full_shape[1],
            feature_features=feature_shape[1],
            lean_theorem="TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.swiglu_two",
        ))
        rewritten.extend(inputs); rewritten_layouts.extend(("zigzag_feature", "zigzag_feature"))
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class ZigzagFeatureUnaryViewCertificate:
    rule_id: str
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    writer_steps: tuple[str, str, str]
    lean_theorem: str


def advance_zigzag_feature_unary_views(plan, frontiers, layouts):
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("zigzag-feature unary frontier/layout lengths disagree")
    by_id = _step_map(plan)
    certificates, rewritten, rewritten_layouts = [], [], []
    for frontier, layout in zip(frontiers, layouts):
        if layout != "zigzag_feature" or len(frontier) != 3 or any(ref.startswith("init:") for ref in frontier):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        try:
            steps = tuple(by_id[ref] for ref in frontier)
        except KeyError:
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if any(step.op not in {"FW_view", "FW_reshape"} for step in steps):
            rewritten.append(frontier); rewritten_layouts.append(layout); continue
        if len({step.op for step in steps}) != 1 or any(
            len(step.input_bindings) != 1 or len(step.input_shapes) != 1
            or tuple(step.input_shapes[0]) != tuple(step.output_shape)
            or tuple(step.parameters) != tuple(step.output_shape)
            for step in steps
        ):
            raise RelationCompositionError("zigzag-feature unary view is not exact shape identity")
        input_refs = _produced_binding_triple(steps, 0)
        input_fact = RelationFactSpec("zigzag_feature", input_refs, gather_dim=1)
        output_fact = RelationFactSpec("zigzag_feature", tuple(frontier), gather_dim=1)
        certificates.append(ZigzagFeatureUnaryViewCertificate(
            rule_id="zigzag-feature-view-id-two-rank",
            input_fact=input_fact, output_fact=output_fact,
            writer_steps=tuple(frontier),
            lean_theorem="TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.view_id_two",
        ))
        rewritten.append(input_refs); rewritten_layouts.append("zigzag_feature")
    return tuple(certificates), tuple(rewritten), tuple(rewritten_layouts)


@dataclass(frozen=True)
class JoinedUnaryViewCertificate:
    rule_id: str
    operator: str
    input_fact: RelationFactSpec
    output_fact: RelationFactSpec
    sm_step_id: str
    pm_step_id: str
    pm_rank: int
    parameters: tuple[int, ...]
    input_shape: tuple[int, ...]
    output_shape: tuple[int, ...]
    lean_theorem: str


def advance_joined_view_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[
    tuple[JoinedUnaryViewCertificate, ...],
    tuple[tuple[str, ...], ...],
    tuple[str, ...],
]:
    """Pull joined equality through two literal, authority-bound FW_view writers."""

    if len(frontiers) != len(layouts):
        raise RelationCompositionError("joined view frontier/layout arity mismatch")
    by_id = {step.step_id: step for step in plan.steps}
    certificates = []
    rewritten = []
    rewritten_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if layout not in {"joined", "joined_zigzag"} or len(frontier) != 2:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        try:
            sm_step, pm_step = (by_id[ref] for ref in frontier)
        except KeyError:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        if sm_step.op != pm_step.op or sm_step.op not in {
            "FW_view", "FW_to", "FW_float", "FW_contiguous", "FW_reshape"
        }:
            rewritten.append(frontier)
            rewritten_layouts.append(layout)
            continue
        operator = sm_step.op
        if sm_step.side != "sm" or pm_step.side != "pm" or int(sm_step.rank) != 0:
            raise RelationCompositionError("joined view writers have incompatible side/rank authority")
        if len(sm_step.input_bindings) != 1 or len(pm_step.input_bindings) != 1:
            raise RelationCompositionError("joined view writers violate unary arity")
        sm_input, pm_input = sm_step.input_bindings[0], pm_step.input_bindings[0]
        if not sm_input.startswith("sm:") or not pm_input.startswith("pm:"):
            raise RelationCompositionError("joined view inputs have incompatible side authority")
        sm_params = tuple(sm_step.parameters)
        pm_params = tuple(pm_step.parameters)
        if sm_params != pm_params:
            raise RelationCompositionError("joined unary literal parameters disagree")
        if len(sm_step.input_shapes) != 1 or len(pm_step.input_shapes) != 1:
            raise RelationCompositionError("joined unary declared input shapes are missing")
        sm_input_shape = tuple(sm_step.input_shapes[0])
        pm_input_shape = tuple(pm_step.input_shapes[0])
        if sm_input_shape != pm_input_shape:
            raise RelationCompositionError("joined unary declared input shapes disagree")
        sm_output_shape = tuple(sm_step.output_shape)
        pm_output_shape = tuple(pm_step.output_shape)
        if sm_output_shape != pm_output_shape:
            raise RelationCompositionError("joined unary declared output shapes disagree")
        if layout == "joined_zigzag":
            if sm_output_shape != sm_input_shape:
                raise RelationCompositionError("joined-zigzag identity writer changes full shape")
            theorem = "TrainVerify.Denote.RelationCompiler.JoinedZigzagRel.view_id_2d"
        elif operator in {"FW_view", "FW_reshape"}:
            if not sm_params or sm_output_shape != sm_params:
                raise RelationCompositionError("joined view/reshape output disagrees with literal parameters")
            theorem = "TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view"
        else:
            if sm_output_shape != sm_input_shape:
                raise RelationCompositionError("joined identity cast changes shape")
            theorem = "TrainVerify.Denote.RelationCompiler.JoinedRel.identity"
        input_fact = RelationFactSpec(layout, (sm_input,), joined_pm_step=pm_input)
        output_fact = RelationFactSpec(
            layout, (sm_step.step_id,), joined_pm_step=pm_step.step_id
        )
        certificates.append(JoinedUnaryViewCertificate(
            rule_id=f"{layout}-{operator.removeprefix('FW_')}-unary",
            operator=operator,
            input_fact=input_fact,
            output_fact=output_fact,
            sm_step_id=sm_step.step_id,
            pm_step_id=pm_step.step_id,
            pm_rank=int(pm_step.rank),
            parameters=sm_params,
            input_shape=sm_input_shape,
            output_shape=sm_output_shape,
            lean_theorem=theorem,
        ))
        rewritten.append((sm_input, pm_input))
        rewritten_layouts.append(layout)
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


def _certificate_identity(item: object) -> tuple[object, ...]:
    """Return an exact, hashable identity including fact/step authority.

    Certificate classes may intentionally define coarse semantic equality.  That
    is not sufficient for proof planning: two applications of the same theorem
    at different graph writers are distinct certificates.  Conversely, an exact
    replay of the same certificate in a later fixed-point round remains a
    legitimate duplicate.
    """

    from dataclasses import fields, is_dataclass

    def freeze(value):
        if is_dataclass(value) and not isinstance(value, type):
            return (
                type(value),
                tuple((field.name, freeze(getattr(value, field.name)))
                      for field in fields(value)),
            )
        if isinstance(value, dict):
            return tuple(sorted((freeze(key), freeze(item)) for key, item in value.items()))
        if isinstance(value, (list, tuple)):
            return tuple(freeze(item) for item in value)
        if isinstance(value, (set, frozenset)):
            return tuple(sorted((freeze(item) for item in value), key=repr))
        try:
            hash(value)
        except TypeError:
            return repr(value)
        return value

    if is_dataclass(item) and not isinstance(item, type):
        payload = tuple(
            (field.name, freeze(getattr(item, field.name))) for field in fields(item)
        )
    elif hasattr(item, "__dict__"):
        payload = tuple(
            sorted((name, freeze(value)) for name, value in vars(item).items())
        )
    else:
        payload = (("value", freeze(item)),)
    return (type(item), payload)


_CERTIFICATE_IDENTITY_CACHE: dict[int, tuple[list[object], int, set[tuple[object, ...]]]] = {}


def _extend_unique_certificates(sink: list[object] | None, items: tuple[object, ...]) -> None:
    if sink is None:
        return
    key = id(sink)
    cached = _CERTIFICATE_IDENTITY_CACHE.get(key)
    if cached is None or cached[0] is not sink or cached[1] > len(sink):
        seen = {_certificate_identity(item) for item in sink}
    else:
        seen = cached[2]
        if cached[1] < len(sink):
            seen.update(_certificate_identity(item) for item in sink[cached[1]:])
    for item in items:
        identity = _certificate_identity(item)
        if identity not in seen:
            seen.add(identity)
            sink.append(item)
    _CERTIFICATE_IDENTITY_CACHE[key] = (sink, len(sink), seen)


def normalize_relation_frontiers(
    plan: ProofPlan,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
    *,
    rules: tuple[str, ...] = ("allreduce_reconstruction_k", "bw_embedding_vocab_k", "bw_embedding_sequence_reduction_k", "bw_sum_k", "bw_softmax_k", "bw_gelu_k", "bw_matmul_k", "bw_linear_dw_column_k", "bw_linear_dw_sharded_k", "bw_linear_dw_reduction_k", "bw_linear_dx_k", "bw_layernorm_param_reduction_k", "bw_layernorm_dx_k", "bw_add_identity_k", "bw_multiref_sum_k", "embedding_vocab_reduction_k", "embedding_sharded_ids_k", "sum_producer_k", "reduction_linear_producer_k", "joined_bw_view", "joined_init_multiref", "zigzag_feature_output_linear", "zigzag_feature_binary", "zigzag_feature_view", "joined_view", "joined_zigzag", "reduce_scatter_reconstruction_k", "allgather_reconstruction_k", "full_producer_k", "output_linear_k", "mix_linear_k", "matmul_output_axis_k", "matmul_head_axis_k", "matmul_query_axis_k", "matmul_contraction_k", "softmax_k", "div_k", "embedding_k", "alltoall_k", "add_k", "multiref_k", "alias", "rms_norm_k", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "embedding_cp2_adapter", "attention_cp2_adapter", "attention", "rotary", "to", "per_head_linear", "mul", "transpose_k", "contiguous_k", "pointwise", "ordinary_moe", "shuffle", "unshuffle", "topk", "zigzag_feature_reduction", "reduction_chunk_boundary", "full_producer_chunk", "add"),
    goal_ir: GoalIR | None = None,
    deduplicate_each_round: bool = False,
    certificate_sink: list[object] | None = None,
    side_condition_sink: list[RelationSideCondition] | None = None,
) -> tuple[tuple[tuple[str, ...], ...], tuple[str, ...]]:
    """Apply registered relation rules to a deterministic fixed point."""
    known = {"allreduce_reconstruction_k", "bw_embedding_vocab_k", "bw_embedding_sequence_reduction_k", "bw_sum_k", "bw_softmax_k", "bw_gelu_k", "bw_matmul_k", "bw_linear_dw_column_k", "bw_linear_dw_sharded_k", "bw_linear_dw_reduction_k", "bw_linear_dx_k", "bw_layernorm_param_reduction_k", "bw_layernorm_dx_k", "bw_add_identity_k", "bw_multiref_sum_k", "embedding_vocab_reduction_k", "embedding_sharded_ids_k", "sum_producer_k", "reduction_linear_producer_k", "joined_bw_view", "joined_init_multiref", "zigzag_feature_output_linear", "zigzag_feature_binary", "zigzag_feature_view", "joined_view", "joined_zigzag", "reduce_scatter_reconstruction_k", "allgather_reconstruction_k", "full_producer_k", "output_linear_k", "mix_linear_k", "matmul_output_axis_k", "matmul_head_axis_k", "matmul_query_axis_k", "matmul_contraction_k", "softmax_k", "div_k", "embedding_k", "alltoall_k", "rms_norm_k", "linear_k", "layernorm_k", "gelu_k", "transpose_k", "contiguous_k", "add_k", "multiref_k", "alias", "rms_norm_k", "rms_norm", "float", "identity_view", "linear", "flatten_3d", "embedding_cp2_adapter", "attention_cp2_adapter", "attention", "rotary", "to", "per_head_linear", "mul", "pointwise", "ordinary_moe", "shuffle", "unshuffle", "topk", "zigzag_feature_reduction", "reduction_chunk_boundary", "full_producer_chunk", "add"}
    known.add("shuffle_k_entry")
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
        if "shuffle_k_entry" in rules:
            if goal_ir is None:
                raise RelationCompositionError("K shuffle requires GoalIR authority")
            _certs, current_frontiers, current_layouts = advance_k_rank_shuffle_entry_frontiers(
                goal_ir, plan, current_frontiers, current_layouts)
            _extend_unique_certificates(certificate_sink, _certs)
        if "allreduce_reconstruction_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_allreduce_reconstruction_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_embedding_vocab_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("bw_embedding_vocab_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_embedding_vocab_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_embedding_sequence_reduction_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("bw_embedding_sequence_reduction_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_embedding_sequence_reduction_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_sum_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("bw_sum_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_sum_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_softmax_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_softmax_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_gelu_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_gelu_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_matmul_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_matmul_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_linear_dw_column_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("bw_linear_dw_column_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_linear_dw_column_sharded_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_linear_dw_sharded_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("bw_linear_dw_sharded_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_linear_dw_sharded_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_linear_dw_reduction_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("bw_linear_dw_reduction_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_linear_dw_reduction_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_linear_dx_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("bw_linear_dx_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_linear_dx_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_layernorm_param_reduction_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("bw_layernorm_param_reduction_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_layernorm_param_reduction_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_layernorm_dx_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("bw_layernorm_dx_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_layernorm_dx_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_add_identity_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_add_identity_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "bw_multiref_sum_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_bw_multiref_sum_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "embedding_vocab_reduction_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("embedding_vocab_reduction_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_vocab_sharded_embedding_producer(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "embedding_sharded_ids_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("embedding_sharded_ids_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_sharded_ids_embedding_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "sum_producer_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_sum_producer_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "reduction_linear_producer_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("reduction_linear_producer_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_reduction_linear_producer_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "joined_bw_view" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_joined_bw_view_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "joined_init_multiref" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_joined_init_multiref_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "zigzag_feature_output_linear" in rules:
            if goal_ir is None:
                raise RelationCompositionError("zigzag_feature_output_linear requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_zigzag_feature_output_linear_frontiers(
                    goal_ir, plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "zigzag_feature_binary" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_zigzag_feature_binary_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "zigzag_feature_view" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_zigzag_feature_unary_views(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "joined_view" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_joined_view_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "joined_zigzag" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_joined_zigzag_allgather_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "reduce_scatter_reconstruction_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_reduce_scatter_reconstruction_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "allgather_reconstruction_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_allgather_reconstruction_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "full_producer_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_full_producer_chunks(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "output_linear_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("output_linear_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_output_sharded_linear_frontiers(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "mix_linear_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_mix_linear_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "matmul_output_axis_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_matmul_output_axis_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "matmul_head_axis_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_matmul_head_axis_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "matmul_query_axis_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_matmul_query_axis_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "matmul_contraction_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_matmul_contraction_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "softmax_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_softmax_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "div_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_div_frontiers(plan, current_frontiers, current_layouts)
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "embedding_k" in rules:
            if goal_ir is None:
                raise RelationCompositionError("embedding_k requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_hidden_sharded_embedding(
                    plan, goal_ir, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "alltoall_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_alltoall_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "rms_norm_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_rms_norm_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "linear_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_linear_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "layernorm_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_layernorm_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "gelu_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_gelu_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "transpose_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_transpose_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "contiguous_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_contiguous_relation_frontiers(
                    plan, current_frontiers, current_layouts,
                    goal_ir=goal_ir if "shuffle_k_entry" in rules else None,
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "add_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_add_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "multiref_k" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_k_rank_multiref_relation_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
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
        if "sharded_flatten_cp2" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_sharded_flatten_to_ordinary_frontiers(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "flatten_3d" in rules:
            _certs, current_frontiers = advance_flatten_3d_relation_frontiers(
                plan, current_frontiers, current_layouts
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "embedding_cp2_adapter" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_embedding_cp2_sharded_to_ordinary(
                    plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "attention_cp2_adapter" in rules:
            _certs, current_frontiers, current_layouts = (
                advance_attention_cp2_schema_adapters(
                    plan, current_frontiers, current_layouts
                )
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
        if "zigzag_feature_reduction" in rules:
            if goal_ir is None:
                raise RelationCompositionError("zigzag_feature_reduction requires GoalIR authority")
            _certs, current_frontiers, current_layouts = (
                advance_zigzag_feature_linear_reduction_boundaries(
                    goal_ir, plan, current_frontiers, current_layouts
                )
            )
            _extend_unique_certificates(certificate_sink, _certs)
        if "reduction_chunk_boundary" in rules:
            _certs, current_frontiers, current_layouts = advance_reduction_chunk_boundaries(
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
    authority_region_ids: tuple[int, ...] | None = None
    transition_specs: tuple[CertificateTransitionSpec, ...] = ()
    coverage_plan: ExactNodeCoveragePlan | None = None
    dependency_plan: TransitionDependencyPlan | None = None
    atomic_schedule: AtomicSchedulePlan | None = None
    dependent_chain_plan: ClosedDependentChainPlan | None = None
    schema_version: int = 7
    graph_coverage_complete: bool = False
    composer_registered: bool = False
    publication_diagnostics: tuple[str, ...] = ()

    @property
    def complete(self) -> bool:
        return (
            not self.unresolved_frontiers
            and not self.unresolved_side_conditions
            and self.graph_coverage_complete
            and self.composer_registered
            and not self.publication_diagnostics
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
    gather_dim: int | None = None
    source_step_triples: tuple[tuple[str, str, str], ...] = ()
    joined_pm_step: str | None = None


def init_lineage_relation_fact(lineage) -> RelationFactSpec:
    """Translate one public InitGoal into an exact ordered K-rank fact."""
    pieces = tuple((int(rank), int(tid)) for rank, tid in lineage.tps)
    shapes = tuple(tuple(int(value) for value in shape) for shape in lineage.tpShapes)
    if not pieces or len(pieces) != len(shapes):
        raise RelationCompositionError("init lineage has empty or mismatched PM authority")
    if tuple(rank for rank, _tid in pieces) != tuple(range(len(pieces))):
        raise RelationCompositionError("init lineage does not preserve ordered ranks")
    refs = (f"init:{int(lineage.ts)}",) + tuple(
        f"init:{tid}" for _rank, tid in pieces
    )
    full_shape = tuple(int(value) for value in lineage.tsShape)
    if bool(lineage.replicated):
        if any(shape != full_shape for shape in shapes):
            raise RelationCompositionError("replicated init lineage violates shape contract")
        if len({tid for _rank, tid in pieces}) != 1:
            raise RelationCompositionError(
                "replicated init lineage lacks cross-rank value authority"
            )
        return RelationFactSpec("replicated", refs)

    gather_dim = 0 if lineage.gatherDim is None else int(lineage.gatherDim)
    shard_shape = shapes[0]
    if any(shape != shard_shape for shape in shapes):
        raise RelationCompositionError("sharded init lineage has unequal shard shapes")
    if shard_shape == (1,):
        if full_shape != (1,):
            raise RelationCompositionError("scalar reduction InitGoal must have full shape [1]")
        return RelationFactSpec("reduction", refs)
    if gather_dim < 0 or gather_dim >= len(shard_shape):
        raise RelationCompositionError("sharded init lineage gather dimension is invalid")
    reconstructed = list(shard_shape)
    reconstructed[gather_dim] *= len(pieces)
    if tuple(reconstructed) != full_shape:
        raise RelationCompositionError("sharded init lineage violates shape contract")
    return RelationFactSpec("sharded", refs, gather_dim=gather_dim)


@dataclass(frozen=True)
class ClosedRelationFactRecord:
    fact_id: str
    source: RelationFactSpec
    kind: str
    sm_tid: int
    pm_tids: tuple[int, ...]
    metadata_tid: int | None
    metadata_region_id: int | None
    full_shape: tuple[int, ...]
    shard_shape: tuple[int, ...]
    gather_dim: int | None = None
    row_shard_shape: tuple[int, ...] | None = None
    source_tid_triples: tuple[tuple[int, int, int], ...] = ()
    joined_pm_tid: int | None = None

    @property
    def pm_rank0_tid(self) -> int:
        if len(self.pm_tids) < 1:
            raise RelationCompositionError("closed relation fact has no PM rank 0")
        return self.pm_tids[0]

    @property
    def pm_rank1_tid(self) -> int:
        if len(self.pm_tids) < 2:
            raise RelationCompositionError("closed relation fact has no PM rank 1")
        return self.pm_tids[1]



def close_k_rank_init_authority(
    ir: GoalIR,
    frontiers: tuple[tuple[str, ...], ...],
    layouts: tuple[str, ...],
) -> tuple[tuple[RelationFactSpec, ...], tuple[tuple[str, ...], ...], tuple[str, ...]]:
    """Discharge only exact ordered public InitGoal relation roots."""
    if len(frontiers) != len(layouts):
        raise RelationCompositionError("K-rank init authority frontier/layout lengths disagree")
    closed = []
    remaining = []
    remaining_layouts = []
    for frontier, layout in zip(frontiers, layouts):
        if not frontier or not all(ref.startswith("init:") for ref in frontier):
            remaining.append(frontier)
            remaining_layouts.append(layout)
            continue
        try:
            sm_tid = int(frontier[0].split(":", 1)[1])
        except (IndexError, ValueError):
            remaining.append(frontier)
            remaining_layouts.append(layout)
            continue
        lineage = ir.init_lineages.get(sm_tid)
        if lineage is None:
            remaining.append(frontier)
            remaining_layouts.append(layout)
            continue
        if layout == "joined" and len(frontier) == 2 and frontier[0] == frontier[1]:
            lineage_pairs = tuple((int(rank), int(tid)) for rank, tid in lineage.tps)
            if (lineage.ts == sm_tid and lineage_pairs == ((0, sm_tid),)
                    and lineage.gatherDim is None and not lineage.replicated
                    and tuple(tuple(shape) for shape in lineage.tpShapes) == (tuple(lineage.tsShape),)):
                closed.append(RelationFactSpec("joined", (frontier[0],), joined_pm_step=frontier[1]))
                continue
        authority = init_lineage_relation_fact(lineage)
        if authority.layout == layout and authority.step_triple == frontier:
            closed.append(authority)
        else:
            remaining.append(frontier)
            remaining_layouts.append(layout)
    return tuple(closed), tuple(remaining), tuple(remaining_layouts)

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
        if isinstance(certificate, (FaithfulShuffleCertificate, KRankShuffleEntryCertificate)):
            source = RelationFactSpec(certificate.post_layout, certificate.output_step_triple)
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
            if fact.layout in {"zigzag", "zigzag_k", "zigzag_feature", "joined_zigzag"} and fact in actual_metadata
        }
        missing_inputs = [
            fact for fact in transition.pre_facts
            if fact.layout in {"zigzag", "zigzag_k", "zigzag_feature", "joined_zigzag"} and fact not in actual_metadata
        ]
        if missing_inputs:
            raise RelationCompositionError(
                f"zigzag metadata input is not live at {transition_id}: {missing_inputs}"
            )
        for fact in transition.post_facts:
            if fact.layout not in {"zigzag", "zigzag_k", "zigzag_feature", "joined_zigzag"}:
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

    pm_init_shapes: dict[int, tuple[int, ...]] = {}
    for lineage in ir.init_lineages.values():
        if len(lineage.tps) != len(lineage.tpShapes):
            raise RelationCompositionError(
                f"init lineage {lineage.ts} has mismatched PM tids/shapes"
            )
        for (_rank, tid), shape in zip(lineage.tps, lineage.tpShapes):
            candidate = tuple(shape)
            previous = pm_init_shapes.get(int(tid))
            if previous is not None and previous != candidate:
                raise RelationCompositionError(f"PM init tid has conflicting shapes: {tid}")
            pm_init_shapes[int(tid)] = candidate

    def resolve(ref: str, expected_side: str) -> tuple[int, tuple[int, ...]]:
        if ref.startswith("init:"):
            try:
                tid = int(ref.split(":", 1)[1])
            except ValueError as exc:
                raise RelationCompositionError(f"invalid init relation reference: {ref}") from exc
            if expected_side == "sm":
                lineage = ir.init_lineages.get(tid)
                if lineage is None:
                    raise RelationCompositionError(f"missing SM init lineage for relation fact: {tid}")
                return tid, tuple(lineage.tsShape)
            if expected_side == "pm":
                shape = pm_init_shapes.get(tid)
                if shape is None:
                    raise RelationCompositionError(f"missing PM init lineage for relation fact: {tid}")
                return tid, shape
            raise RelationCompositionError(f"unsupported init relation side: {expected_side}")
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

    ordered = sorted(specs, key=lambda fact: (
        fact.layout,
        fact.step_triple,
        -1 if fact.gather_dim is None else fact.gather_dim,
        fact.source_step_triples,
        "" if fact.joined_pm_step is None else fact.joined_pm_step,
    ))
    result = []
    for ordinal, fact in enumerate(ordered):
        if fact.layout in {"sharded", "chunked", "reduction", "replicated", "zigzag_feature", "zigzag_k"}:
            if len(fact.step_triple) < 2:
                raise RelationCompositionError(
                    f"K-rank {fact.layout} relation fact requires one SM and at least one PM reference"
                )
        elif fact.layout in {"joined", "joined_zigzag"}:
            if len(fact.step_triple) != 1 or fact.joined_pm_step is None:
                raise RelationCompositionError(
                    f"{fact.layout} relation fact requires one SM reference and one PM joined output"
                )
        elif len(fact.step_triple) != 3:
            raise RelationCompositionError(
                f"two-rank relation fact requires one SM and two PM references: {fact.step_triple}"
            )
        sm_tid, full_shape = resolve(fact.step_triple[0], "sm")
        metadata_tid = None
        metadata_region_id = None
        row_shard_shape = None
        source_tid_triples = ()
        joined_pm_tid = None
        if fact.layout in {"joined", "joined_zigzag"}:
            joined_pm_tid, joined_shape = resolve(fact.joined_pm_step, "pm")
            if joined_shape != full_shape:
                raise RelationCompositionError("joined relation output shape disagrees with SM output")
            pm_tids = ()
            shard0_shape = full_shape
            pm0_tid = joined_pm_tid
            pm1_tid = joined_pm_tid
        else:
            pm_resolved = tuple(resolve(ref, "pm") for ref in fact.step_triple[1:])
            pm_tids = tuple(item[0] for item in pm_resolved)
            shard_shapes = tuple(item[1] for item in pm_resolved)
            shard0_shape = shard_shapes[0]
            if any(shape != shard0_shape for shape in shard_shapes[1:]):
                raise RelationCompositionError(
                    f"relation fact PM shard shapes disagree: {fact.step_triple}"
                )
            pm0_tid = pm_tids[0]
            pm1_tid = pm_tids[1] if len(pm_tids) > 1 else pm_tids[0]
        if fact.layout in {"zigzag", "zigzag_k", "zigzag_feature", "joined_zigzag"}:
            metadata_tid = actual_metadata.get(fact)
            if metadata_tid is None:
                raise RelationCompositionError(
                    f"zigzag relation fact lacks directional metadata authority: {fact.step_triple}"
                )
            region = region_by_frontier.get(fact.step_triple)
            if region is None:
                candidates = tuple(
                    item for item in relation.zigzag_regions
                    if metadata_tid in item.alias_tids
                )
                if len(candidates) == 1:
                    region = candidates[0]
            if region is None:
                raise RelationCompositionError(
                    f"zigzag relation fact has no unique metadata region: {fact.step_triple}"
                )
            if metadata_tid not in region.alias_tids:
                raise RelationCompositionError(
                    f"zigzag metadata tid is outside its public alias region: {metadata_tid}"
                )
            metadata_region_id = region.region_id
        if fact.layout == "joined_indexed_stack_dim1":
            if fact.gather_dim != 1 or not fact.source_step_triples or fact.joined_pm_step is None:
                raise RelationCompositionError(
                    "indexed-stack fact must carry gather dimension 1 and nonempty ordered sources"
                )
            if len(full_shape) != 3 or len(shard0_shape) != 3:
                raise RelationCompositionError("indexed-stack outputs must have rank-3 shapes")
            if full_shape[0] != len(fact.source_step_triples) or shard0_shape[0] != len(fact.source_step_triples):
                raise RelationCompositionError("indexed-stack source count disagrees with output shapes")
            if full_shape[1] != 2 * shard0_shape[1] or full_shape[2] != shard0_shape[2]:
                raise RelationCompositionError("indexed-stack output shapes are not a truthful dim-1 gather")
            source_tid_triples = []
            for source_triple in fact.source_step_triples:
                source_sm_tid, source_full_shape = resolve(source_triple[0], "sm")
                source_pm0_tid, source_shard0_shape = resolve(source_triple[1], "pm")
                source_pm1_tid, source_shard1_shape = resolve(source_triple[2], "pm")
                if source_shard0_shape != source_shard1_shape:
                    raise RelationCompositionError("indexed-stack source shard shapes disagree")
                if source_full_shape != full_shape[1:] or source_shard0_shape != shard0_shape[1:]:
                    raise RelationCompositionError(
                        "indexed-stack source shapes do not reconstruct the declared output tails"
                    )
                source_tid_triples.append((source_sm_tid, source_pm0_tid, source_pm1_tid))
            source_tid_triples = tuple(source_tid_triples)
            joined_pm_tid, joined_shape = resolve(fact.joined_pm_step, "pm")
            if joined_shape != full_shape or joined_pm_tid in {pm0_tid, pm1_tid}:
                raise RelationCompositionError("indexed-stack joined output is not a distinct full-shape PM tensor")
        elif fact.layout == "joined_zigzag":
            if joined_pm_tid is None or len(full_shape) < 1 or full_shape[0] % 2 != 0:
                raise RelationCompositionError("joined-zigzag output/full shape authority mismatch")
            row_shard_shape = (full_shape[0] // 2, *full_shape[1:])
            shard0_shape = row_shard_shape
        elif fact.layout == "joined_ordinary":
            if fact.joined_pm_step is None:
                raise RelationCompositionError("joined ordinary fact lacks its PM collective output")
            joined_pm_tid, joined_shape = resolve(fact.joined_pm_step, "pm")
            if joined_shape != full_shape or joined_pm_tid in {pm0_tid, pm1_tid}:
                raise RelationCompositionError("joined ordinary output is not a distinct full-shape PM tensor")
        elif fact.layout == "joined":
            pass
        elif fact.layout == "replicated":
            if shard0_shape != full_shape:
                raise RelationCompositionError(
                    "K-rank replicated relation requires every PM shape to equal the SM shape"
                )
        elif fact.layout == "reduction":
            if not pm_tids:
                raise RelationCompositionError("K-rank reduction relation requires nonempty contributions")
            if shard0_shape != full_shape:
                raise RelationCompositionError(
                    "K-rank reduction contributions must have the exact SM full shape"
                )
        elif fact.layout in {"sharded", "chunked"}:
            dim = fact.gather_dim
            if dim is None or dim < 0 or dim >= len(shard0_shape):
                raise RelationCompositionError(
                    f"K-rank sharded relation has invalid gather dimension: {dim}"
                )
            expected_full = list(shard0_shape)
            expected_full[dim] *= len(pm_tids)
            if tuple(expected_full) != full_shape:
                raise RelationCompositionError(
                    "K-rank sharded relation full shape is not the declared equal-shard gather"
                )
        elif fact.layout == "zigzag_k":
            if (not shard0_shape or any(d <= 0 for d in (*full_shape, *shard0_shape))
                    or full_shape != (len(pm_tids)*shard0_shape[0], *shard0_shape[1:])
                    or region.num_ranks != len(pm_tids) or region.total_tokens != full_shape[0]):
                raise RelationCompositionError("K zigzag metadata rank/token/shape mismatch")
        elif fact.layout == "zigzag_feature":
            if fact.gather_dim != 1 or len(full_shape) < 2 or len(shard0_shape) != len(full_shape):
                raise RelationCompositionError("zigzag-feature relation requires rank≥2 dim-1 feature sharding")
            if full_shape[0] % 2 != 0:
                raise RelationCompositionError("zigzag-feature canonical row count is not two-rank divisible")
            expected_full = list(shard0_shape)
            expected_full[1] *= len(pm_tids)
            if tuple(expected_full) != full_shape:
                raise RelationCompositionError("zigzag-feature shards do not reconstruct the feature axis")
            row_shard_shape = (full_shape[0] // 2, *full_shape[1:])
        elif fact.layout not in {"ordinary", "zigzag", "label_chunks"}:
            raise RelationCompositionError(f"unsupported closed relation layout: {fact.layout}")
        else:
            source_tid_triples = ()

        result.append(ClosedRelationFactRecord(
            fact_id=f"fact_{ordinal:06d}",
            source=fact,
            kind=fact.layout,
            sm_tid=sm_tid,
            pm_tids=pm_tids,
            metadata_tid=metadata_tid,
            metadata_region_id=metadata_region_id,
            full_shape=full_shape,
            shard_shape=shard0_shape,
            row_shard_shape=row_shard_shape,
            gather_dim=fact.gather_dim,
            source_tid_triples=source_tid_triples,
            joined_pm_tid=joined_pm_tid,
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
class ClosedLabelBoundFactRecord:
    fact_id: str
    side: str
    tid: int
    length: int
    upper_bound: int
    kind: str = "label_bound"


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
        ClosedGatherFactRecord | ClosedPackedCuFactRecord |
        ClosedLabelBoundFactRecord, ...
    ]
    anchor_fact: ClosedTensorShapeFactRecord
    states: tuple[ClosedRelationStateRecord, ...]
    segments: tuple[ClosedDependentSegmentRecord, ...]
    initial_state_id: str
    terminal_state_id: str
    terminal_target_fact_id: str
    retained_target_fact_ids: tuple[str, ...]
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
        if not set(self.retained_target_fact_ids) <= set(self.states[-1].fact_ids):
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
    protected_sources: tuple[RelationFactSpec, ...] = (),
    primary_target_source: RelationFactSpec | None = None,
    retain_all_authority: bool = False,
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

    for transition in relation.transition_specs:
        for requirement in transition.authority_requirements:
            if requirement.kind == "tensor_eq":
                if len(requirement.sides) != 2 or len(requirement.tids) != 2:
                    raise RelationCompositionError("tensor_eq authority requirement is malformed")
                left_side, right_side = requirement.sides
                left_tid, right_tid = requirement.tids
                item = ClosedTensorEqFactRecord(
                    fact_id=(f"authority_transition_eq_{left_side}_{left_tid}_"
                             f"{right_side}_{right_tid}"),
                    left_side=left_side, left_tid=left_tid,
                    right_side=right_side, right_tid=right_tid,
                )
                key = ("tensor_eq", left_side, left_tid, right_side, right_tid)
                side_tids = ((left_side, left_tid), (right_side, right_tid))
            elif requirement.kind == "tensor_shape":
                if len(requirement.sides) != 1 or len(requirement.tids) != 1 or not requirement.shape:
                    raise RelationCompositionError("tensor_shape authority requirement is malformed")
                side, tid = requirement.sides[0], requirement.tids[0]
                item = ClosedTensorShapeFactRecord(
                    fact_id=f"authority_transition_shape_{side}_{tid}",
                    side=side, tid=tid, shape=requirement.shape, init_goal_id=tid,
                )
                key = ("tensor_shape", side, tid, requirement.shape)
                side_tids = ((side, tid),)
            elif requirement.kind == "label_bound":
                if (len(requirement.sides) != 1 or len(requirement.tids) != 1
                        or requirement.length is None or requirement.upper_bound is None):
                    raise RelationCompositionError("label_bound authority requirement is malformed")
                side, tid = requirement.sides[0], requirement.tids[0]
                item = ClosedLabelBoundFactRecord(
                    fact_id=f"authority_label_bound_{side}_{tid}",
                    side=side, tid=tid, length=requirement.length,
                    upper_bound=requirement.upper_bound,
                )
                key = ("label_bound", side, tid, requirement.length, requirement.upper_bound)
                side_tids = ((side, tid),)
            else:
                raise RelationCompositionError(
                    f"unknown transition authority requirement {requirement.kind!r}"
                )
            add_authority(item, key, side_tids)

    facts_by_region = {}
    for fact in facts:
        if fact.metadata_region_id is not None:
            facts_by_region.setdefault(fact.metadata_region_id, set()).add(fact.metadata_tid)
    authority_region_ids = relation.authority_region_ids
    authority_regions = (
        relation.zigzag_regions if authority_region_ids is None else
        tuple(region for region in relation.zigzag_regions
              if region.region_id in set(authority_region_ids))
    )
    for region in sorted(authority_regions, key=lambda item: item.region_id):
        add_authority(
            ClosedPackedCuFactRecord(
                fact_id=f"authority_packed_cu_{region.region_id:06d}",
                side="pm", tid=region.contract_metadata_tid,
                total_tokens=region.total_tokens, num_ranks=region.num_ranks,
            ),
            ("packed_cu", region.contract_metadata_tid, region.total_tokens, region.num_ranks),
            (("pm", region.contract_metadata_tid),),
        )
        actual_tids = set(facts_by_region.get(region.region_id, set()))
        actual_tids.update(region.alias_tids)
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
        if type(certificate) is not InitChunkBoundaryCertificate:
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
        pm_tids = tuple(tid for _rank, tid in certificate.lineage_pm_rank_tids)
        for pm_tid in pm_tids:
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
        if type(certificate) is PerHeadLinearRelationCertificate:
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
        elif type(certificate) is FrontierAttentionCertificate:
            for binding in certificate.metadata_bindings:
                if not binding.startswith("init:"):
                    raise RelationCompositionError("attention metadata is not an external InitGoal binding")
                tid = int(binding.split(":", 1)[1])
                lineage = ir.init_lineages.get(tid)
                if lineage is None or tuple(lineage.tps) != ((0, tid),):
                    raise RelationCompositionError(
                        f"attention metadata lacks singleton InitGoal lineage: {tid}"
                    )
                replicated_tids.add(tid)
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
        if not isinstance(certificate, (FaithfulShuffleCertificate, KRankShuffleEntryCertificate)):
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

    external_sources = {
        fact for transition in relation.transition_specs for fact in transition.pre_facts
        if fact not in producer
    }
    for source in external_sources:
        record = record_by_source[source]
        if record.kind not in {"sharded", "replicated", "reduction", "joined"}:
            raise RelationCompositionError(
                f"closed chain external relation is not immutable InitGoal authority: {source}"
            )
        if not _is_external_relation_fact(source):
            raise RelationCompositionError(
                f"closed chain external relation references graph writers: {source}"
            )
        lineage = ir.init_lineages.get(record.sm_tid)
        if source.layout == "joined":
            exact_init = (
                source.step_triple == (f"init:{record.sm_tid}",)
                and source.joined_pm_step == f"init:{record.sm_tid}"
                and lineage is not None
                and tuple(lineage.tps) == ((0, record.sm_tid),)
                and tuple(tuple(shape) for shape in lineage.tpShapes) == (tuple(lineage.tsShape),)
                and not lineage.replicated and lineage.gatherDim is None
            )
        else:
            exact_init = lineage is not None and init_lineage_relation_fact(lineage) == source
        if not exact_init:
            raise RelationCompositionError(
                f"closed chain external relation does not match exact InitGoal authority: {source}"
            )
        if record.sm_tid not in ir.full_init_goal_ids:
            raise RelationCompositionError(
                f"closed chain external relation lacks full InitGoal authority: {record.sm_tid}"
            )

    consumed = {fact for transition in relation.transition_specs for fact in transition.pre_facts}
    if primary_target_source is None:
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
    else:
        target_source = primary_target_source
    target_fact_id = record_by_source[target_source].fact_id
    protected = {target_source, *protected_sources}
    missing_protected = protected - set(record_by_source)
    if missing_protected:
        raise RelationCompositionError(
            f"protected terminal relation facts are not materialized: {sorted(map(repr, missing_protected))}"
        )
    unproduced_protected = protected - set(producer)
    if unproduced_protected:
        raise RelationCompositionError(
            f"protected terminal relation facts are not produced: {sorted(map(repr, unproduced_protected))}"
        )
    retained_target_fact_ids = tuple(sorted(record_by_source[fact].fact_id for fact in protected))

    components = {item.component_id: item for item in schedule.components}
    transition_order = {item: index for index, item in enumerate(dependency.order)}
    ordered_components = [components[item] for item in schedule.order]
    metadata_region_by_contract = {
        region.contract_metadata_tid: region.region_id
        for region in relation.zigzag_regions
    }
    metadata_authority_regions = {
        (actual_tid, region.contract_metadata_tid): region.region_id
        for region in relation.zigzag_regions
        for actual_tid in {region.contract_metadata_tid, *region.alias_tids}
    }
    authority_last_use = {}
    for fact in authority_facts:
        if fact.kind == "tensor_eq":
            side_tids = ((fact.left_side, fact.left_tid), (fact.right_side, fact.right_tid))
        elif fact.kind == "tensor_shape":
            side_tids = ((fact.side, fact.tid),)
        elif fact.kind == "gather":
            side_tids = (("sm", fact.sm_tid), ("pm", fact.pm_rank0_tid),
                         ("pm", fact.pm_rank1_tid))
        elif fact.kind == "label_bound":
            side_tids = ((fact.side, fact.tid),)
        else:
            side_tids = ()
        uses = []
        for index, component in enumerate(ordered_components):
            sm_inputs = {tid for node in ir.sm_nodes[slice(*component.sm_range)] for tid in node.ins}
            pm_inputs = {tid for node in ir.pm_nodes[slice(*component.pm_range)] for tid in node.ins}
            if any(tid in (sm_inputs if side == "sm" else pm_inputs) for side, tid in side_tids):
                uses.append(index)
            for transition_id in component.transition_ids:
                for requirement in transition_by_id[transition_id].authority_requirements:
                    if fact.kind == "tensor_eq" and requirement.kind == "tensor_eq" and (
                        requirement.sides == (fact.left_side, fact.right_side)
                        and requirement.tids == (fact.left_tid, fact.right_tid)
                    ) or fact.kind == "tensor_shape" and requirement.kind == "tensor_shape" and (
                        requirement.sides == (fact.side,) and requirement.tids == (fact.tid,)
                        and requirement.shape == fact.shape
                    ) or fact.kind == "label_bound" and requirement.kind == "label_bound" and (
                        requirement.sides == (fact.side,) and requirement.tids == (fact.tid,)
                        and requirement.length == fact.length
                        and requirement.upper_bound == fact.upper_bound
                    ):
                        uses.append(index)
        metadata_region_id = None
        metadata_tid = None
        if fact.kind == "packed_cu":
            metadata_region_id = metadata_region_by_contract.get(fact.tid)
            if metadata_region_id is None:
                raise RelationCompositionError(
                    f"packed-cu authority lacks one exact region: {fact.tid}"
                )
        elif fact.kind == "tensor_eq" and (
            fact.left_side, fact.right_side
        ) == ("pm", "pm"):
            metadata_region_id = metadata_authority_regions.get(
                (fact.left_tid, fact.right_tid)
            )
            if metadata_region_id is not None:
                metadata_tid = fact.left_tid
        if metadata_region_id is not None:
            for index, component in enumerate(ordered_components):
                sources = [
                    source
                    for transition_id in component.transition_ids
                    for source in (
                        *transition_by_id[transition_id].pre_facts,
                        *transition_by_id[transition_id].post_facts,
                    )
                ]
                if any(
                    record_by_source[source].metadata_region_id == metadata_region_id
                    and (
                        metadata_tid is None
                        or record_by_source[source].metadata_tid == metadata_tid
                    )
                    for source in sources
                ):
                    uses.append(index)
        authority_last_use[fact.fact_id] = (
            len(ordered_components) if retain_all_authority else max(uses, default=0)
        )
    live = {
        anchor.fact_id,
        *(item.fact_id for item in authority_facts),
        *(record_by_source[source].fact_id for source in external_sources),
    }
    available_sources = set(external_sources)
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
            if fact in protected or any(
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
        retained_target_fact_ids=retained_target_fact_ids,
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
    authority_requirements: tuple[TransitionAuthorityRequirement, ...] = ()
    fact_only: bool = False
    certificate_digest: str = ""


def _fact(layout: str, refs: tuple[str, ...]) -> RelationFactSpec:
    if layout in {"joined", "joined_zigzag"}:
        if len(refs) != 2:
            raise RelationCompositionError(f"{layout} fact requires one SM and one joined PM ref")
        return RelationFactSpec(layout, (refs[0],), joined_pm_step=refs[1])
    if layout not in {"ordinary", "zigzag", "label_chunks"}:
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


_register_closed_rule_specs(
    ClosedRuleSpec(
        "bw-add-identity-sharded-k-rank", KRankBWAddIdentityCertificate,
        ("TrainVerify.Denote.bw_add2_fst_same_shape", "TrainVerify.Denote.bw_add2_snd_same_shape"),
        "BW_add", "bw_add_identity_renderer:render_closed_k_rank_bw_add_identity_segment",
        (),
    ),
    ClosedRuleSpec(
        "bw-embedding-sequence-reduction-rank4", KRankBWEmbeddingSequenceReductionCertificate,
        ("TrainVerify.Denote.bw_embedding_seqchunk_4shards_1_8_32",),
        "BW_embedding", "bw_embedding_sequence_renderer:render_closed_k_rank_bw_embedding_sequence_segment",
        (),
    ),
    ClosedRuleSpec(
        "bw-embedding-vocab-sharded-k-rank", KRankBWEmbeddingVocabCertificate,
        ("TrainVerify.Denote.bw_embedding_eq_allGather_offset_4shards",),
        "BW_embedding", "bw_embedding_vocab_renderer:render_closed_k_rank_bw_embedding_vocab_segment",
        (),
    ),
    ClosedRuleSpec(
        "bw-gelu-pointwise-sharded-k-rank", KRankBWGeluCertificate,
        ("TrainVerify.Denote.bw_gelu_allGatherPrimDimN_eq",),
        "BW_gelu", "bw_gelu_renderer:render_closed_k_rank_bw_gelu_segment",
        (),
    ),
    ClosedRuleSpec(
        "bw-layernorm-dx-dim1-k-rank", KRankBWLayernormDxCertificate,
        ("TrainVerify.Denote.bw_layernorm_dx_allGatherPrimDimN_dim1_3d",),
        "BW_layernorm", "bw_layernorm_dx_renderer:render_closed_k_rank_bw_layernorm_dx_segment",
        ("denote.KRankBWLayernorm",),
    ),
    ClosedRuleSpec(
        "bw-linear-dw-input-column-sharded-k-rank", KRankBWLinearDwColumnShardedCertificate,
        ("TrainVerify.Denote.bw_linear_dw_input_allGatherPrimDimN_dim2_rank3",),
        "BW_linear", "bw_linear_dx_column_renderer:render_closed_k_rank_bw_linear_dw_column_segment",
        ("denote.KRankBWLinearDwColumn",),
    ),
    ClosedRuleSpec(
        "bw-linear-dx-column-sharded-k-rank", KRankBWLinearDxCertificate,
        ("TrainVerify.Denote.bw_linear_dx_weight_allGatherPrimDimN_dim1_rank3",),
        "BW_linear", "bw_linear_dx_column_renderer:render_closed_k_rank_bw_linear_dx_column_segment",
        ("denote.KRankBWLinearDxColumn",),
    ),
    ClosedRuleSpec(
        "bw-linear-dx-row-reduction-k-rank", KRankBWLinearDxCertificate,
        ("TrainVerify.Denote.bw_linear_dx_allGatherPrimDimN_dim2_rank3",),
        "BW_linear", "bw_linear_dx_renderer:render_closed_k_rank_bw_linear_dx_segment",
        ("denote.KRankBWLinearDx",),
    ),
    ClosedRuleSpec(
        "bw-linear-dx-row-reduction-rank4", KRankBWLinearDxCertificate,
        (
            "TrainVerify.Denote.bw_linear_dx_tp_split_dim2_4_g134",
            "TrainVerify.Denote.bw_linear_dx_tp_split_dim2_4_g178",
        ),
        "BW_linear", "bw_linear_dx_renderer:render_closed_k_rank_bw_linear_dx_segment",
        (),
    ),
    ClosedRuleSpec(
        "bw-linear-dx-sequence-sharded-rank4", KRankBWLinearDxCertificate,
        (
            "TrainVerify.Denote.bw_linear_dx_dp_split_dim1_4_g169",
            "TrainVerify.Denote.bw_linear_dx_dp_split_dim1_4_g143",
        ),
        "BW_linear", "transpose_linear_transpose_renderer:render_closed_transpose_linear_transpose_segment",
        (),
    ),
    ClosedRuleSpec(
        "bw-multiref-sum-sharded-k-rank", KRankBWMultirefSumCertificate,
        ("TrainVerify.Denote.tensorSum_allGather_dim_K",),
        "BW_multiref", "bw_multiref_sum_renderer:render_closed_k_rank_bw_multiref_sum_segment",
        ("denote.KRankBWMultiref",),
    ),
    ClosedRuleSpec(
        "bw-sum-scalar-broadcast-dim2-k-rank", KRankBWSumCertificate,
        ("TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3",),
        "BW_sum", "bw_sum_renderer:render_closed_k_rank_bw_sum_segment",
        ("denote.KRankBWSum",),
    ),
    ClosedRuleSpec(
        "bw-view-joined", JoinedBWViewCertificate,
        ("TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view",),
        "BW_view", "bw_view_joined_renderer:render_closed_joined_bw_view_segment",
        (),
    ),
    ClosedRuleSpec(
        "alltoall-k-rank-layout-transport", KRankAllToAllRelationCertificate,
        ("TrainVerify.Denote.allGatherPrimDimN_allToAllPrimWithDims_ofFn",),
        "AllToAllPrimWithDims", "composer:render_closed_k_rank_alltoall_segment",
        (),
    ),
    ClosedRuleSpec(
        "cross-dp-wred-reconstruction-k-rank", KRankAllReduceReconstructionCertificate,
        ("TrainVerify.Denote.RelationCompiler.ReductionRel.to_joined_allReduce",),
        "CROSS_DP_WRED", "cross_dp_wred_renderer:render_closed_cross_dp_wred_segment",
        (),
    ),
    ClosedRuleSpec(
        "reduce-scatter-reconstruction-k-rank", KRankReduceScatterReconstructionCertificate,
        ("TrainVerify.Denote.allGatherPrimDimN_chunks_ofFn",),
        "ReduceScatterPrim", "reduce_scatter_renderer:render_closed_k_rank_reduce_scatter_segment",
        (),
    ),
    ClosedRuleSpec(
        "zigzag-allgather-joined-two-rank", JoinedZigzagAllGatherCertificate,
        ("TrainVerify.Denote.RelationCompiler.JoinedZigzagRel.of_allGather",),
        "AllGatherPrim", "joined_zigzag_allgather_renderer:render_closed_joined_zigzag_allgather_segment",
        (),
    ),
    ClosedRuleSpec(
        "linear-output-sharded-two-rank-2d", KRankOutputShardedLinearCertificate,
        ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_linear_output_dim1_two_2d",),
        "FW_mix_precision_linear", "output_linear_2d_renderer:render_closed_output_sharded_linear_2d_segment", (),
    ),
    ClosedRuleSpec(
        "float-ordinary-two-rank", FrontierFloatCertificate,
        ("TrainVerify.Denote.fw_float_allGather0_commute_2",),
        "FW_float", "composer:render_closed_float_segment", (),
    ),
    ClosedRuleSpec(
        "fw-shuffle-sharded-to-zigzag-k", KRankShuffleEntryCertificate,
        ("TrainVerify.Denote.RelationCompiler.ZigzagKRel.of_sharded",),
        "FW_maybe_shuffle", "k_shuffle_entry_renderer:render_closed_k_shuffle_entry_segment", (),
    ),
    ClosedRuleSpec(
        "bw-unshuffle-sharded-to-zigzag-k", KRankShuffleEntryCertificate,
        ("TrainVerify.Denote.RelationCompiler.ZigzagKRel.of_sharded",),
        "BW_maybe_unshuffle", "k_shuffle_entry_renderer:render_closed_k_shuffle_entry_segment", (),
    ),
    ClosedRuleSpec(
        "faithful-maybe-shuffle-ordinary-to-zigzag-two-rank", FaithfulShuffleCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.of_sources",),
        "FW_maybe_shuffle", "composer:render_closed_shuffle_entry_segment", (),
    ),
    ClosedRuleSpec(
        "bw-maybe-unshuffle-ordinary-to-zigzag-two-rank", FaithfulShuffleCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.of_sources",),
        "BW_maybe_unshuffle", "composer:render_closed_shuffle_entry_segment", (),
    ),
    ClosedRuleSpec(
        "zigzag-to-ordinary-unshuffle-two-rank", FrontierUnshuffleCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.to_gather2_unshuffle",),
        "FW_maybe_unshuffle", "composer:render_closed_unshuffle_segment", (),
    ),
    ClosedRuleSpec(
        "bw-maybe-shuffle-zigzag-to-ordinary-two-rank", FrontierUnshuffleCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.to_gather2_unshuffle",),
        "BW_maybe_shuffle", "composer:render_closed_unshuffle_segment", (),
    ),
    ClosedRuleSpec(
        "indexed-stack-gather-two-rank", IndexedStackGatherCertificate,
        ("TrainVerify.Denote.RelationCompiler.fw_stack_allGather0_dim1_commute_2d_element",),
        None, "composer:render_closed_indexed_stack_segment", (),
    ),
    ClosedRuleSpec(
        "swiglu-sharded-two-rank-dim1", KRankBinaryRelationCertificate,
        ("TrainVerify.Denote.RelationCompiler.ShardedRel.fw_swiglu_dim1_two_2d",),
        "FW_swiglu", "sharded_swiglu_renderer:render_closed_sharded_swiglu_segment", (),
    ),
    ClosedRuleSpec(
        "rms-norm-joined-two-rank", FrontierRMSNormCertificate,
        ("TrainVerify.Denote.RelationCompiler.JoinedRel.rms_norm",),
        "FW_rms_norm", "joined_rms_renderer:render_closed_joined_rms_segment", (),
    ),
    ClosedRuleSpec(
        "rms-norm-joined_zigzag-two-rank", FrontierRMSNormCertificate,
        ("TrainVerify.Denote.RelationCompiler.JoinedZigzagRel.rms_norm",),
        "FW_rms_norm", "joined_zigzag_rms_renderer:render_closed_joined_zigzag_rms_segment", (),
    ),
    ClosedRuleSpec(
        "zigzag-feature-linear-dim1-allreduce-chunks-cp2", ZigzagFeatureLinearReductionCertificate,
        ("TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.mix_precision_linear_dim1_allReduce_chunks_cp2",),
        None, "zigzag_feature_linear_reduction_renderer:render_closed_zigzag_feature_linear_reduction_segment", (),
    ),
    ClosedRuleSpec(
        "zigzag-feature-swiglu-two-rank", ZigzagFeatureBinaryCertificate,
        ("TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.swiglu_two",),
        "FW_swiglu", "zigzag_feature_swiglu_renderer:render_closed_zigzag_feature_swiglu_segment", (),
    ),
    ClosedRuleSpec(
        "zigzag-feature-view-id-two-rank", ZigzagFeatureUnaryViewCertificate,
        ("TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.view_id_two",),
        None, "zigzag_feature_view_renderer:render_closed_zigzag_feature_view_segment", (),
    ),
    ClosedRuleSpec(
        "zigzag-feature-output-linear-two-rank", ZigzagFeatureOutputLinearCertificate,
        ("TrainVerify.Denote.RelationCompiler.ZigzagFeatureRel.output_sharded_linear_two",),
        "FW_mix_precision_linear", "zigzag_feature_output_linear_renderer:render_closed_zigzag_feature_output_linear_segment", (),
    ),
    ClosedRuleSpec(
        "rotary-embedding-two-output-ordinary-two-rank", RotaryRelationCertificate,
        ("TrainVerify.Denote.fw_rotary_embedding_allGather0_commute_2",),
        "FW_rotary_embedding", "composer:render_closed_rotary_segment", (),
    ),
    ClosedRuleSpec(
        "mix-precision-linear-ordinary-two-rank", FrontierLinearCertificate,
        ("TrainVerify.Denote.fw_mix_precision_linear_allGather0_commute_2",),
        "FW_mix_precision_linear", "composer:render_closed_linear_segment", (),
    ),
    ClosedRuleSpec(
        "mix-precision-linear-zigzag-two-rank", FrontierLinearCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.mix_precision_linear",),
        "FW_mix_precision_linear", "composer:render_closed_linear_segment", (),
    ),
    ClosedRuleSpec(
        "elementwise-add-ordinary-two-rank", FrontierAddCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.elemwiseAdd_allGather0_commute_cp2",),
        "FW_add", "composer:render_closed_binary_segment", (),
    ),
    ClosedRuleSpec(
        "elementwise-add-zigzag-two-rank", FrontierAddCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.add",),
        "FW_add", "composer:render_closed_binary_segment", (),
    ),
    ClosedRuleSpec(
        "broadcast-mul-ordinary-two-rank", FrontierMulCertificate,
        ("TrainVerify.Denote.RelationCompiler.Ordinary2Rel.mul_broadcast_col1",),
        "FW_mul", "composer:render_closed_binary_segment", (),
    ),
    ClosedRuleSpec(
        "broadcast-mul-zigzag-two-rank", FrontierMulCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.mul_broadcast_col1",),
        "FW_mul", "composer:render_closed_binary_segment", (),
    ),
    ClosedRuleSpec(
        "swiglu-ordinary-two-rank", FrontierPointwiseCertificate,
        ("TrainVerify.Denote.RelationCompiler.Ordinary2Rel.swiglu",),
        "FW_swiglu", "composer:render_closed_binary_segment", (),
    ),
    ClosedRuleSpec(
        "swiglu-zigzag-two-rank", FrontierPointwiseCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.swiglu",),
        "FW_swiglu", "composer:render_closed_binary_segment", (),
    ),
    ClosedRuleSpec(
        "glu-ordinary-two-rank", FrontierPointwiseCertificate,
        ("TrainVerify.Denote.RelationCompiler.Ordinary2Rel.glu",),
        "FW_glu", "composer:render_closed_binary_segment", (),
    ),
    ClosedRuleSpec(
        "glu-zigzag-two-rank", FrontierPointwiseCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.glu",),
        "FW_glu", "composer:render_closed_binary_segment", (),
    ),
    ClosedRuleSpec(
        "float-zigzag-two-rank", FrontierFloatCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.fw_float",),
        "FW_float", "composer:render_closed_unary_segment", (),
    ),
    ClosedRuleSpec(
        "identity-view-ordinary-two-rank", FrontierIdentityViewCertificate,
        ("TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id",),
        "FW_view", "composer:render_closed_unary_segment", (),
    ),
    ClosedRuleSpec(
        "identity-view-zigzag-two-rank", FrontierIdentityViewCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_id",),
        "FW_view", "composer:render_closed_unary_segment", (),
    ),
    ClosedRuleSpec(
        "identity-reshape-ordinary-two-rank", FrontierIdentityViewCertificate,
        ("TrainVerify.Denote.RelationCompiler.Ordinary2Rel.view_id",),
        "FW_reshape", "composer:render_closed_unary_segment", (),
    ),
    ClosedRuleSpec(
        "identity-reshape-zigzag-two-rank", FrontierIdentityViewCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_id",),
        "FW_reshape", "composer:render_closed_unary_segment", (),
    ),
    ClosedRuleSpec(
        "flatten-3d-ordinary-two-rank", FrontierFlatten3DCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.fw_view_allGather0_commute_cp2",),
        "FW_reshape", "composer:render_closed_unary_segment", (),
    ),
    ClosedRuleSpec(
        "flatten-3d-zigzag-two-rank", FrontierFlatten3DCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.view_3d_to_2d",),
        "FW_reshape", "composer:render_closed_unary_segment", (),
    ),
    ClosedRuleSpec(
        "init-lineage-alias-chunks-two-rank-dim0", InitAliasChunkCertificate,
        (
            "TrainVerify.Denote.RelationCompiler.ChunkedRel.of_chunks_two",
            "TrainVerify.Denote.RelationCompiler.ShardedRel.of_chunks_two",
        ),
        "ChunkPrim", "init_alias_chunk_renderer:render_closed_init_alias_chunk_segment", (),
    ),
    ClosedRuleSpec(
        "init-lineage-alias-chunks-two-rank-dim1", InitAliasChunkCertificate,
        (
            "TrainVerify.Denote.RelationCompiler.ChunkedRel.of_chunks_two",
            "TrainVerify.Denote.RelationCompiler.ShardedRel.of_chunks_two",
        ),
        "ChunkPrim", "init_alias_chunk_renderer:render_closed_init_alias_chunk_segment", (),
    ),
    ClosedRuleSpec(
        "rms-norm-ordinary-two-rank", FrontierRMSNormCertificate,
        (
            "TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core",
            "TrainVerify.Denote.ZigzagCollective.fw_rms_norm_allGather0_commute_2_core_3d",
        ),
        "FW_rms_norm", "composer:render_closed_rms_norm_segment", (),
    ),
    ClosedRuleSpec(
        "rms-norm-zigzag-two-rank", FrontierRMSNormCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.rms_norm",),
        "FW_rms_norm", "composer:render_closed_rms_norm_segment", (),
    ),
    ClosedRuleSpec(
        "attention-ordinary-qkv-two-rank", FrontierAttentionCertificate,
        ("TrainVerify.Denote.GeneratedPatterns.applyNodeRingAttn_sliding_window_reconstruction_2_of_buddy_pair",),
        "FW_attn_sliding_window", "composer:render_closed_attention_segment", (),
    ),
    ClosedRuleSpec(
        "attention-zigzag-qkv-two-rank", FrontierAttentionCertificate,
        (
            "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.attn_zigzag",
            "TrainVerify.Denote.GeneratedPatterns.Zigzag2Rel.attn_zigzag_sharded_kv",
        ),
        "FW_attn_zigzag", "composer:render_closed_attention_segment", (),
    ),
)


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
    import hashlib
    import json
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
        registered = CLOSED_RULE_REGISTRY.get(getattr(cert, "rule_id", ""))
        if registered is not None:
            if type(cert) is not registered.certificate_type:
                raise RelationCompositionError(
                    f"registered rule {registered.rule_id} has the wrong certificate type"
                )
            certificate_op = getattr(cert, "op", registered.op)
            if (certificate_op != registered.op
                    or getattr(cert, "lean_theorem", None) not in registered.lean_theorems):
                raise RelationCompositionError(
                    f"registered rule {registered.rule_id} has inconsistent backend identity"
                )
        pre: tuple[RelationFactSpec, ...]
        post: tuple[RelationFactSpec, ...]
        footprint_groups: tuple[tuple[str, ...], ...]
        authority_requirements: tuple[TransitionAuthorityRequirement, ...] = ()
        fact_only = False
        if type(cert) is CP2ShardedToOrdinaryCertificate:
            if (cert.input_fact.layout != "sharded" or cert.input_fact.gather_dim != 0
                    or cert.output_fact.layout != "ordinary"
                    or cert.input_fact.step_triple != cert.output_fact.step_triple):
                raise RelationCompositionError("malformed CP2 sharded-to-ordinary adapter")
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ()
            fact_only = True
        elif type(cert) is CP2OrdinaryToShardedCertificate:
            if (cert.input_fact.layout != "ordinary"
                    or cert.output_fact.layout != "sharded"
                    or cert.output_fact.gather_dim != 0
                    or cert.input_fact.step_triple != cert.output_fact.step_triple):
                raise RelationCompositionError("malformed CP2 ordinary-to-sharded adapter")
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ()
            fact_only = True
        elif type(cert) is ShardedFlattenToOrdinaryCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = (cert.writer_steps,)
        elif type(cert) in (MultirefAliasCertificate, FrontierIdentityViewCertificate,
                FrontierLinearCertificate, FrontierRMSNormCertificate,
                FrontierFloatCertificate, FrontierFlatten3DCertificate,
                FrontierToCertificate):
            pre = (_fact(cert.relation_kind, cert.input_step_triple),)
            if type(cert) in (FrontierLinearCertificate, FrontierRMSNormCertificate):
                pre += (cert.weight_fact,)
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
        elif type(cert) is InitAliasChunkCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = (tuple(cert.chunk_steps),)
        elif type(cert) is ZigzagFeatureLinearReductionCertificate:
            pre = (cert.input_fact, cert.weight_fact)
            post = (cert.output_fact,)
            footprint_groups = (
                (cert.sm_linear_step,), tuple(cert.sm_output_identity_steps),
                tuple(cert.pm_linear_steps), (cert.pm_allreduce_step,),
                (cert.pm_output_identity_step,), tuple(cert.pm_chunk_steps),
            )
        elif type(cert) is ReductionChunkBoundaryCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = (
                tuple(cert.sm_identity_steps),
                (cert.pm_allreduce_step,),
                tuple(cert.pm_identity_steps),
                tuple(cert.pm_chunk_steps),
            )
        elif type(cert) is FullProducerChunkCertificate:
            pre = (_fact(cert.pre_layout, cert.input_step_triple),)
            post = (_fact(cert.post_layout, cert.output_step_triple),)
            footprint_groups = (
                (cert.sm_operator_step,),
                (cert.pm_full_operator_step,),
                tuple(cert.pm_chunk_steps),
                tuple(cert.sm_identity_chain),
                tuple(cert.pm_identity_chain),
                tuple(cert.sm_output_identity_chain),
                tuple(cert.pm_output_identity_chain),
                (cert.pm_allgather_step,),
            )
        elif type(cert) is PerHeadLinearRelationCertificate and cert.relation_kind == "sharded":
            pre = (RelationFactSpec("sharded", cert.input_relation_step_triple, gather_dim=0),)
            post = (RelationFactSpec("sharded", cert.output_step_triple, gather_dim=0),)
            footprint_groups = (cert.output_step_triple,)
        elif type(cert) is PerHeadLinearRelationCertificate:
            pre = (_fact(cert.relation_kind, cert.input_relation_step_triple),)
            post = (_fact(cert.relation_kind, cert.output_step_triple),)
            footprint_groups = (cert.output_step_triple,)
        elif type(cert) is RotaryRelationCertificate:
            pre = tuple(_fact(cert.relation_kind, refs) for refs in cert.input_relation_step_triples)
            post = tuple(_fact(cert.relation_kind, refs) for refs in cert.output_step_triples)
            footprint_groups = tuple(cert.output_step_triples)
        elif type(cert) is KRankShuffleEntryCertificate:
            pre, post = (cert.input_fact,), (cert.output_fact,)
            footprint_groups = (cert.output_step_triple,)
        elif type(cert) is FrontierUnshuffleCertificate or type(cert) is FaithfulShuffleCertificate:
            pre = (_fact(cert.pre_layout, cert.input_step_triple),)
            post = (_fact(cert.post_layout, cert.output_step_triple),)
            footprint_groups = (cert.output_step_triple,)
        elif type(cert) is InitChunkBoundaryCertificate:
            post_refs = (f"init:{cert.sm_tid}", *tuple(cert.chunk_step_pair))
            pre = ()
            post = (
                _fact(cert.relation_kind, post_refs),
                _fact("label_chunks", post_refs),
            )
            footprint_groups = (tuple(cert.chunk_step_pair),)
        elif type(cert) is KRankSumAllReduceTerminalCertificate:
            pre = (cert.input_fact,)
            post = (RelationFactSpec(
                "joined",
                (cert.sm_sum_step,),
                joined_pm_step=cert.pm_allreduce_step,
            ),)
            footprint_groups = (
                (cert.sm_sum_step,), cert.pm_sum_steps, (cert.pm_allreduce_step,)
            )
        elif type(cert) is KRankBWEmbeddingVocabCertificate:
            pre = (cert.gradient_fact, cert.ids_fact, cert.weight_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankVocabShardedEmbeddingProducerCertificate:
            pre = (cert.weight_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
            authority_requirements = (
                TransitionAuthorityRequirement(
                    "tensor_eq", ("sm", "pm"), (cert.ids_tid, cert.ids_tid),
                ),
                TransitionAuthorityRequirement(
                    "tensor_shape", ("pm",), (cert.ids_tid,), cert.ids_shape,
                ),
            )
        elif type(cert) is KRankShardedIdsEmbeddingCertificate:
            pre = ()
            post = (cert.ids_chunks_fact, cert.output_fact)
            footprint_groups = (
                (cert.sm_embedding_step,), cert.pm_chunk_steps,
                cert.pm_embedding_steps,
            )
            authority_requirements = (
                TransitionAuthorityRequirement(
                    "tensor_eq", ("sm", "pm"), (cert.ids_tid, cert.ids_tid),
                ),
                TransitionAuthorityRequirement(
                    "tensor_shape", ("pm",), (cert.ids_tid,), cert.ids_full_shape,
                ),
                TransitionAuthorityRequirement(
                    "tensor_eq", ("sm", "pm"), (cert.weight_tid, cert.weight_tid),
                ),
                TransitionAuthorityRequirement(
                    "tensor_shape", ("pm",), (cert.weight_tid,), cert.weight_shape,
                ),
            )
        elif type(cert) is KRankSumProducerCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_sum_step,), cert.pm_sum_steps)
        elif type(cert) is KRankReductionLinearProducerCertificate:
            pre = (cert.activation_fact, cert.weight_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_linear_step,), cert.pm_linear_steps)
        elif type(cert) is KRankHiddenShardedEmbeddingCertificate:
            pre = (cert.weight_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
            authority_requirements = (
                TransitionAuthorityRequirement(
                    "tensor_eq", ("sm", "pm"), (cert.ids_tid, cert.ids_tid),
                ),
                TransitionAuthorityRequirement(
                    "tensor_shape", ("pm",), (cert.ids_tid,), cert.ids_shape,
                ),
            )
        elif type(cert) is KRankAllReduceReconstructionCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.pm_allreduce_step,),)
        elif type(cert) is KRankReduceScatterReconstructionCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = (cert.pm_step_ids,)
        elif type(cert) is KRankAllGatherReconstructionCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.pm_allgather_step,),)
        elif type(cert) is ZigzagFeatureOutputLinearCertificate:
            pre = (cert.activation_fact, cert.weight_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is ZigzagFeatureBinaryCertificate:
            pre = cert.input_facts
            post = (cert.output_fact,)
            footprint_groups = (cert.writer_steps,)
        elif type(cert) is ZigzagFeatureUnaryViewCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = (cert.writer_steps,)
        elif type(cert) is JoinedInitMultirefGroupCertificate:
            pre = (cert.input_fact,)
            post = cert.output_facts
            footprint_groups = (cert.pm_step_ids,)
        elif type(cert) is JoinedInitMultirefCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.pm_step_id,),)
        elif type(cert) is JoinedZigzagAllGatherCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.pm_allgather_step,),)
        elif type(cert) is JoinedUnaryViewCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), (cert.pm_step_id,))
        elif type(cert) is KRankFullProducerChunksCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            # The joined pre-fact is produced by the preceding semantic writer
            # transition.  This reconstruction transition owns only the K chunks;
            # replaying either full producer would invalidate that closed authority.
            footprint_groups = (cert.pm_chunk_steps,)
        elif type(cert) is KRankOutputShardedLinearCertificate:
            pre = (cert.activation_fact, cert.weight_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) in (KRankMatmulOutputAxisCertificate, KRankMatmulQueryAxisCertificate):
            pre = (cert.first_operand_fact, cert.second_operand_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankSoftmaxCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankMatmulHeadAxisCertificate:
            pre = (cert.first_operand_fact, cert.second_operand_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankMatmulContractionCertificate:
            pre = (cert.first_operand_fact, cert.second_operand_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankDivCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankContiguousRelationCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankTransposeRelationCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankLocalRelationCertificate:
            pre = (cert.input_fact, *cert.external_facts)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
            authority_requirements = () if cert.external_facts else tuple(
                requirement
                for tid, shape in zip(cert.external_tids, cert.external_shapes)
                for requirement in (
                    TransitionAuthorityRequirement(
                        "tensor_eq", ("sm", "pm"), (tid, tid),
                    ),
                    TransitionAuthorityRequirement(
                        "tensor_shape", ("pm",), (tid,), shape,
                    ),
                )
            )
        elif type(cert) is KRankMultirefRelationCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBinaryRelationCertificate:
            pre = cert.input_facts
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWEmbeddingSequenceReductionCertificate:
            pre = (cert.gradient_fact, cert.ids_chunks_fact, cert.weight_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWSoftmaxCertificate:
            pre = (cert.gradient_fact, cert.activation_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is JoinedBWViewCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), (cert.pm_step_id,))
        elif type(cert) is KRankBWSumCertificate:
            pre = (cert.gradient_fact, cert.activation_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWGeluCertificate:
            pre = (cert.gradient_fact, cert.activation_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWMatmulCertificate:
            pre = cert.input_facts
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWLinearDwColumnShardedCertificate:
            pre = (cert.gradient_fact, cert.activation_fact, cert.weight_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWLinearDwShardedCertificate:
            pre = (cert.gradient_fact, cert.activation_fact, cert.weight_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWLinearDwReductionCertificate:
            pre = (cert.gradient_fact, cert.activation_fact, cert.weight_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWLinearDxCertificate:
            pre = cert.input_facts
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWLayernormParamReductionCertificate:
            pre = (cert.gradient_fact, cert.activation_fact, cert.gamma_fact, cert.beta_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWLayernormDxCertificate:
            pre = (cert.gradient_fact, cert.activation_fact, cert.gamma_fact, cert.beta_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWMultirefSumCertificate:
            pre = cert.input_facts
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankBWAddIdentityCertificate:
            pre = (cert.input_fact, cert.operand_fact)
            post = (cert.output_fact,)
            footprint_groups = ((cert.sm_step_id,), cert.pm_step_ids)
        elif type(cert) is KRankAllToAllRelationCertificate:
            pre = (cert.input_fact,)
            post = (cert.output_fact,)
            footprint_groups = (cert.pm_step_ids,)
        elif type(cert) is HiddenShardedEmbeddingAllToAllCertificate:
            post_refs = (cert.sm_embedding_step, *tuple(cert.alltoall_steps))
            pre = ()
            post = (_fact("ordinary", post_refs),)
            footprint_groups = (
                (cert.sm_embedding_step,), tuple(cert.pm_embedding_steps), tuple(cert.alltoall_steps)
            )
        elif type(cert) is InnerChunkCEGatherCertificate:
            post_refs = (cert.sm_ce_step, *tuple(cert.pm_ce_steps))
            pre_items = [_fact("ordinary", cert.input_step_triple)]
            if cert.output_projection == ".fst":
                if cert.label_chunk_step_triple is None:
                    raise RelationCompositionError("CE .fst transition lacks exact label chunks")
                pre_items.append(_fact("label_chunks", cert.label_chunk_step_triple))
            pre = tuple(pre_items)
            post = (RelationFactSpec(
                "joined_ordinary", post_refs, joined_pm_step=cert.pm_gather_step
            ),)
            weight_tid = int(cert.weight_binding.split(":", 1)[1])
            label_tid = int(cert.label_binding.split(":", 1)[1])
            authority_requirements = (
                TransitionAuthorityRequirement("tensor_eq", ("sm", "pm"), (weight_tid, weight_tid)),
                TransitionAuthorityRequirement("tensor_shape", ("pm",), (weight_tid,), cert.weight_shape),
            )
            if cert.output_projection == ".fst":
                authority_requirements += (
                    TransitionAuthorityRequirement("tensor_eq", ("sm", "pm"), (label_tid, label_tid)),
                    TransitionAuthorityRequirement("tensor_shape", ("pm",), (label_tid,), cert.label_shape),
                    TransitionAuthorityRequirement(
                        "label_bound", ("pm",), (label_tid,),
                        length=cert.full_rows, upper_bound=cert.label_bound,
                    ),
                )
            elif cert.label_independence_theorem is None:
                raise RelationCompositionError("CE .snd transition lacks its label-independence adapter")
            footprint_groups = ((cert.sm_ce_step,), tuple(cert.pm_ce_steps), (cert.pm_gather_step,))
        elif type(cert) is IndexedStackGatherCertificate:
            pre = tuple(_fact("ordinary", refs) for refs in cert.layer_step_triples)
            post_refs = (cert.sm_stack_step, *tuple(cert.pm_stack_steps))
            post = (RelationFactSpec(
                "joined_indexed_stack_dim1",
                post_refs,
                gather_dim=1,
                source_step_triples=cert.layer_step_triples,
                joined_pm_step=cert.pm_gather_step,
            ),)
            footprint_groups = (
                (cert.sm_stack_step,), tuple(cert.pm_stack_steps), (cert.pm_gather_step,)
            )
        else:
            raise RelationCompositionError(
                f"no explicit transition adapter for certificate type {type(cert).__name__}"
            )

        sm_nodes, pm_nodes = _merge_footprints(*footprint_groups)
        if type(cert) is ZigzagFeatureLinearReductionCertificate:
            pm_nodes = tuple(sorted(set(pm_nodes) | set(cert.pm_output_identity_writer_indices)))
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
        preserve_operand_roles = type(cert) in {
            KRankMatmulHeadAxisCertificate,
            KRankLocalRelationCertificate,
            ZigzagFeatureOutputLinearCertificate,
            ZigzagFeatureBinaryCertificate,
            ZigzagFeatureLinearReductionCertificate,
            JoinedInitMultirefGroupCertificate,
        }
        certificate_digest = hashlib.sha256(json.dumps(
            {"type": type(cert).__name__, "fields": asdict(cert)},
            separators=(",", ":"), sort_keys=True,
        ).encode()).hexdigest()
        transitions.append(CertificateTransitionSpec(
            transition_id=f"{ordinal:06d}:{type(cert).__name__}:{cert.rule_id}",
            rule_id=cert.rule_id,
            pre_facts=tuple(pre) if preserve_operand_roles else tuple(sorted(set(pre))),
            post_facts=tuple(post) if preserve_operand_roles else tuple(sorted(set(post))),
            sm_node_indices=sm_nodes,
            pm_node_indices=pm_nodes,
            lean_theorem=lean_theorem,
            certificate_digest=certificate_digest,
            authority_requirements=authority_requirements,
            fact_only=fact_only,
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


def _is_external_relation_fact(fact: RelationFactSpec) -> bool:
    try:
        from .relation_authority_policy import is_pure_init_relation_authority
    except ImportError:
        from relation_authority_policy import is_pure_init_relation_authority
    return is_pure_init_relation_authority(fact)


def build_transition_dependency_plan(
    transitions: tuple[CertificateTransitionSpec, ...],
    *,
    external_pre_facts: frozenset[RelationFactSpec] = frozenset(),
) -> TransitionDependencyPlan:
    """Reverse the backward frontier certificates into a deterministic DAG."""

    import heapq

    invalid_external = tuple(
        fact for fact in external_pre_facts
        if not _is_external_relation_fact(fact)
    )
    if invalid_external:
        raise RelationCompositionError(
            f"external pre-fact is not pure init authority: {invalid_external[0]}"
        )

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
                if fact in external_pre_facts:
                    continue
                same_triple = tuple(
                    produced for produced in producers
                    if produced.step_triple == fact.step_triple
                )
                raise RelationCompositionError(
                    f"relation pre-fact has no producer: {item.transition_id} {fact}; "
                    f"same-triple producers={same_triple}"
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
    *,
    external_pre_facts: frozenset[RelationFactSpec] = frozenset(),
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
    dependency = build_transition_dependency_plan(
        transitions, external_pre_facts=external_pre_facts
    )
    dependency_by_consumer = dict(dependency.dependencies)

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
        empty = not item.sm_node_indices and not item.pm_node_indices
        if empty and not item.fact_only:
            raise RelationCompositionError(
                f"semantic transition has empty footprint: {item.transition_id}"
            )
        if item.fact_only and not empty:
            raise RelationCompositionError(
                f"fact-only transition owns graph nodes: {item.transition_id}"
            )
        if item.fact_only:
            if len(item.pre_facts) != 1 or len(item.post_facts) != 1:
                raise RelationCompositionError(
                    f"fact-only transition requires one pre/post fact: {item.transition_id}"
                )
            before, after = item.pre_facts[0], item.post_facts[0]
            if (before.step_triple != after.step_triple
                    or before.source_step_triples != after.source_step_triples
                    or before.joined_pm_step != after.joined_pm_step):
                raise RelationCompositionError(
                    f"fact-only transition changes graph provenance: {item.transition_id}"
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
    for item in transitions:
        if not item.fact_only:
            continue
        producers = dependency_by_consumer.get(item.transition_id, ())
        if len(producers) != 1:
            raise RelationCompositionError(
                f"fact-only transition requires one exact producer: {item.transition_id}"
            )
        union(item.transition_id, producers[0])

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
        edges.update((left, right) for left, right in itertools.pairwise(stream) if left != right)
        for index, item in enumerate(stream):
            if not item.startswith("frame:"):
                continue
            right = next((candidate for candidate in stream[index + 1:] if candidate in semantic_items), None)
            left = next((candidate for candidate in reversed(stream[:index]) if candidate in semantic_items), None)
            owner = right or left or min(semantic_items)
            edges.add((item, owner))
            edges.add((owner, item))

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

    authority_payload = {
        "sm": [node_authority_fingerprint(node) for node in ir.sm_nodes],
        "pm": [node_authority_fingerprint(node) for node in ir.pm_nodes],
    }
    transition_payload = {
        "schema_version": 2,
        "transitions": [asdict(item) for item in transitions],
    }
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
            fingerprint = node_authority_fingerprint(node)
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


def compile_k_shuffle_entry_boundary(ir: GoalIR, proof: ProofPlan) -> RelationPlan:
    """Compile a shared zigzag-K post fact, NOT an ordinary LineageGoal terminal."""
    sink = []
    frontiers, layouts = normalize_relation_frontiers(
        proof, (tuple(proof.target_steps),), ("zigzag_k",),
        rules=("shuffle_k_entry", "contiguous_k"), goal_ir=ir, certificate_sink=sink)
    _closed, frontiers, layouts = close_k_rank_init_authority(ir, frontiers, layouts)
    certs = tuple(sink)
    target_entries = tuple(
        cert for cert in certs
        if isinstance(cert, KRankShuffleEntryCertificate)
        and cert.output_step_triple == tuple(proof.target_steps)
    )
    if len(target_entries) != 1:
        raise RelationCompositionError("K shuffle boundary requires one target entry certificate")
    regions, _ = resolve_zigzag_metadata_regions(ir, certs, (), ())
    transitions = build_certificate_transition_specs(proof, certs)
    external = select_unproduced_external_pre_facts(transitions)
    base = RelationPlan(
        family="cp-shuffle-k-entry-boundary", terminal_rule_id="cp-shuffle-k-entry-boundary",
        synchronized_steps=(), certificates=certs,
        unresolved_frontiers=frontiers, unresolved_layouts=layouts,
        unresolved_side_conditions=(), zigzag_regions=regions,
        transition_specs=transitions, coverage_plan=build_exact_node_coverage_plan(ir, transitions),
        dependency_plan=build_transition_dependency_plan(transitions, external_pre_facts=external),
        atomic_schedule=build_atomic_schedule(ir, transitions, external_pre_facts=external))
    if frontiers or layouts:
        return base
    return replace(base, dependent_chain_plan=build_closed_dependent_chain_plan(ir, proof, base))


def compile_relation_plan(
    ir: GoalIR,
    proof: ProofPlan,
    *,
    peel_aliases: bool = True,
    deduplicate_frontiers: bool = True,
) -> RelationPlan:
    """Compile registered terminal relation families without hiding backbone gaps."""
    by_target_step = _step_map(proof)
    if (ir.pm_num_ranks != 2 and proof.target_steps
            and all(ref in by_target_step for ref in proof.target_steps)
            and {by_target_step[ref].op for ref in proof.target_steps} in
                ({"FW_maybe_shuffle"}, {"BW_maybe_unshuffle"})):
        return compile_k_shuffle_entry_boundary(ir, proof)
    sharded_embedding_error = None
    try:
        terminal_embedding = match_k_rank_sharded_ids_embedding_terminal(ir, proof)
    except RelationCompositionError as exc:
        sharded_embedding_error = exc
    else:
        certificate_tuple = (terminal_embedding,)
        transition_specs = build_certificate_transition_specs(proof, certificate_tuple)
        coverage_plan = build_exact_node_coverage_plan(ir, transition_specs)
        external_pre_facts = frozenset(
            fact for transition in transition_specs for fact in transition.pre_facts
            if _is_external_relation_fact(fact)
        )
        dependency_plan = build_transition_dependency_plan(
            transition_specs, external_pre_facts=external_pre_facts,
        )
        atomic_schedule = build_atomic_schedule(
            ir, transition_specs, external_pre_facts=external_pre_facts,
        )
        base_plan = RelationPlan(
            family="sequence-sharded-embedding-k-rank",
            terminal_rule_id=terminal_embedding.rule_id,
            synchronized_steps=(), certificates=certificate_tuple,
            unresolved_frontiers=(), unresolved_layouts=(),
            unresolved_side_conditions=(), zigzag_regions=(),
            transition_specs=transition_specs, coverage_plan=coverage_plan,
            dependency_plan=dependency_plan, atomic_schedule=atomic_schedule,
        )
        return replace(
            base_plan,
            dependent_chain_plan=build_closed_dependent_chain_plan(
                ir, proof, base_plan
            ),
        )
    specialized_gather_terminal = False
    if getattr(proof.relation.kind, "value", proof.relation.kind) == "gather":
        for matcher in (
            match_indexed_stack_gather_two_rank,
            match_inner_chunk_ce_projection_gather_two_rank,
        ):
            try:
                matcher(ir, proof)
            except RelationCompositionError:
                if (
                    matcher is match_inner_chunk_ce_projection_gather_two_rank
                    and is_inner_chunk_ce_projection_gather_topology(proof)
                ):
                    raise
                continue
            specialized_gather_terminal = True
            break
    if (getattr(proof.relation.kind, "value", proof.relation.kind) == "gather"
            and not specialized_gather_terminal):
        by_step = _step_map(proof)
        joined_target = (
            len(proof.target_steps) == 2
            and len(proof.relation.pm_pieces) == 1
            and by_step[proof.target_steps[0]].side == "sm"
            and by_step[proof.target_steps[1]].side == "pm"
            and tuple(by_step[proof.target_steps[0]].output_shape)
                == tuple(by_step[proof.target_steps[1]].output_shape)
        )
        seed_layout = "joined" if joined_target else "sharded"
        target_fact = (
            RelationFactSpec(
                "joined", (proof.target_steps[0],),
                joined_pm_step=proof.target_steps[1],
            )
            if joined_target else
            RelationFactSpec(
                "sharded", tuple(proof.target_steps),
                gather_dim=int(proof.relation.gather_dim),
            )
        )
        compiled_certificates: list[object] = []
        frontiers, layouts = normalize_relation_frontiers(
            proof, (tuple(proof.target_steps),), (seed_layout,),
            rules=("allreduce_reconstruction_k", "bw_embedding_vocab_k", "bw_embedding_sequence_reduction_k", "bw_sum_k", "bw_softmax_k", "bw_gelu_k", "bw_matmul_k", "bw_linear_dw_column_k", "bw_linear_dw_sharded_k", "bw_linear_dw_reduction_k", "bw_linear_dx_k", "bw_layernorm_param_reduction_k", "bw_layernorm_dx_k", "bw_add_identity_k", "bw_multiref_sum_k", "embedding_vocab_reduction_k",
                   "embedding_sharded_ids_k", "sum_producer_k",
                   "reduction_linear_producer_k", "joined_bw_view", "joined_init_multiref", "zigzag_feature_output_linear", "zigzag_feature_binary", "zigzag_feature_view", "joined_view", "joined_zigzag",
                   "reduce_scatter_reconstruction_k", "allgather_reconstruction_k", "full_producer_k",
                   "output_linear_k", "mix_linear_k", "matmul_output_axis_k",
                   "matmul_head_axis_k", "matmul_query_axis_k",
                   "matmul_contraction_k", "softmax_k", "div_k",
                   "embedding_k", "alltoall_k", "rms_norm_k", "linear_k", "layernorm_k",
                   "gelu_k", "transpose_k", "contiguous_k", "add_k",
                   "multiref_k"),
            goal_ir=ir, certificate_sink=compiled_certificates,
            deduplicate_each_round=True,
        )
        _closed_init_authority, frontiers, layouts = close_k_rank_init_authority(
            ir, frontiers, layouts
        )
        if deduplicate_frontiers:
            frontiers, layouts = deduplicate_relation_frontiers(frontiers, layouts)
        certificate_tuple = tuple(compiled_certificates)
        transition_specs = build_certificate_transition_specs(proof, certificate_tuple)
        if target_fact not in {
            fact for transition in transition_specs for fact in transition.post_facts
        }:
            raise RelationCompositionError("direct gather fixed point did not preserve target authority")
        coverage_plan = build_exact_node_coverage_plan(ir, transition_specs)
        external_pre_facts = select_unproduced_external_pre_facts(
            transition_specs
        )
        dependency_plan = build_transition_dependency_plan(
            transition_specs, external_pre_facts=external_pre_facts,
        )
        atomic_schedule = build_atomic_schedule(
            ir, transition_specs, external_pre_facts=external_pre_facts,
        )
        base_plan = RelationPlan(
            family="direct-gather-k-rank", terminal_rule_id="direct-gather-k-rank",
            synchronized_steps=(), certificates=certificate_tuple,
            unresolved_frontiers=frontiers, unresolved_layouts=layouts,
            unresolved_side_conditions=(), zigzag_regions=(),
            transition_specs=transition_specs, coverage_plan=coverage_plan,
            dependency_plan=dependency_plan, atomic_schedule=atomic_schedule,
        )
        if frontiers or layouts:
            return base_plan
        return replace(
            base_plan,
            dependent_chain_plan=build_closed_dependent_chain_plan(ir, proof, base_plan),
        )
    k_terminal_error = None
    try:
        terminal_certificates, frontiers, layouts = (
            advance_k_rank_allreduce_reconstruction_frontiers(
                proof, (tuple(proof.target_steps),), ("joined",)
            )
        )
        if len(terminal_certificates) != 1:
            raise RelationCompositionError("target is not one rank-0 AllReduce writer")
        terminal_k = terminal_certificates[0]
    except RelationCompositionError as exc:
        k_terminal_error = exc
    else:
        compiled_certificates: list[object] = [terminal_k]
        if peel_aliases:
            frontiers, layouts = normalize_relation_frontiers(
                proof,
                frontiers,
                layouts,
                rules=("allreduce_reconstruction_k", "embedding_vocab_reduction_k", "sum_producer_k", "reduction_linear_producer_k", "joined_bw_view", "joined_init_multiref", "zigzag_feature_output_linear", "zigzag_feature_binary", "zigzag_feature_view", "joined_view", "joined_zigzag", "reduce_scatter_reconstruction_k", "allgather_reconstruction_k", "full_producer_k", "output_linear_k", "mix_linear_k", "matmul_output_axis_k", "matmul_head_axis_k", "matmul_query_axis_k", "matmul_contraction_k", "softmax_k", "div_k", "embedding_k", "alltoall_k", "rms_norm_k", "linear_k", "layernorm_k", "gelu_k", "transpose_k", "contiguous_k", "add_k", "multiref_k"),
                goal_ir=ir,
                certificate_sink=compiled_certificates,
                deduplicate_each_round=True,
            )
        _closed_init_authority, frontiers, layouts = close_k_rank_init_authority(
            ir, frontiers, layouts
        )
        if deduplicate_frontiers:
            frontiers, layouts = deduplicate_relation_frontiers(frontiers, layouts)
        certificate_tuple = tuple(compiled_certificates)
        transition_specs = build_certificate_transition_specs(proof, certificate_tuple)
        coverage_plan = build_exact_node_coverage_plan(ir, transition_specs)
        external_pre_facts = select_unproduced_external_pre_facts(
            transition_specs
        )
        dependency_plan = build_transition_dependency_plan(
            transition_specs,
            external_pre_facts=external_pre_facts,
        )
        atomic_schedule = build_atomic_schedule(
            ir, transition_specs,
            external_pre_facts=external_pre_facts,
        )
        base_plan = RelationPlan(
            family="ordered-allreduce-writer-k-rank",
            terminal_rule_id=terminal_k.rule_id,
            synchronized_steps=(),
            certificates=certificate_tuple,
            unresolved_frontiers=frontiers,
            unresolved_layouts=layouts,
            unresolved_side_conditions=(),
            zigzag_regions=(),
            transition_specs=transition_specs,
            coverage_plan=coverage_plan,
            dependency_plan=dependency_plan,
            atomic_schedule=atomic_schedule,
        )
        if frontiers or layouts:
            return base_plan
        return replace(
            base_plan,
            dependent_chain_plan=build_closed_dependent_chain_plan(ir, proof, base_plan),
        )
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
                ir, tuple(compiled_certificates), unresolved_frontiers,
                tuple(unresolved_layouts), tuple(layers)
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
        external_pre_facts = frozenset(
            fact
            for transition in transition_specs
            for fact in transition.pre_facts
            if _is_external_relation_fact(fact)
        )
        dependency_plan = build_transition_dependency_plan(
            transition_specs, external_pre_facts=external_pre_facts
        )
        atomic_schedule = build_atomic_schedule(
            ir, transition_specs, external_pre_facts=external_pre_facts
        )
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
            f"no registered relation family: ksum={k_terminal_error}; stack={stack_error}; ce={ce_error}"
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
        weight_facts = tuple(dict.fromkeys(
            certificate.weight_fact
            for certificate in compiled_certificates
            if type(certificate) in {FrontierLinearCertificate, FrontierRMSNormCertificate}
        ))
        weight_frontiers = tuple(
            (fact.step_triple[0], fact.joined_pm_step)
            for fact in weight_facts
            if fact.layout == "joined" and fact.joined_pm_step is not None
        )
        frontiers, layouts = deduplicate_relation_frontiers(
            (*frontiers, *weight_frontiers),
            (*layouts, *("joined" for _ in weight_frontiers)),
        )
        frontiers, layouts = normalize_relation_frontiers(
            proof, frontiers, layouts,
            rules=("joined_init_multiref",),
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
    init_alias_chunk_certificates, frontiers, layouts = close_init_alias_chunk_boundaries(
        ir, proof, frontiers, layouts
    )
    _extend_unique_certificates(compiled_certificates, init_alias_chunk_certificates)
    alias_input_frontiers = tuple(
        (certificate.input_fact.step_triple[0], certificate.input_fact.joined_pm_step)
        for certificate in init_alias_chunk_certificates
    )
    if alias_input_frontiers:
        frontiers, layouts = deduplicate_relation_frontiers(
            (*frontiers, *alias_input_frontiers),
            (*layouts, *("joined" for _ in alias_input_frontiers)),
        )
        frontiers, layouts = normalize_relation_frontiers(
            proof, frontiers, layouts,
            rules=("joined_init_multiref",),
            goal_ir=ir,
            certificate_sink=compiled_certificates,
            side_condition_sink=unresolved_side_conditions,
            deduplicate_each_round=True,
        )
    closed_init_facts, frontiers, layouts = close_k_rank_init_authority(
        ir, frontiers, layouts
    )
    if terminal_ce.label_chunk_step_triple is not None:
        label_chunk_certificates, missing_label_frontiers, missing_label_layouts = (
            close_init_chunk_boundaries(
                ir, proof, (terminal_ce.label_chunk_step_triple,), ("ordinary",)
            )
        )
        if missing_label_frontiers or missing_label_layouts or len(label_chunk_certificates) != 1:
            raise RelationCompositionError(
                "CE .fst exact label ChunkPrim producers did not close"
            )
        _extend_unique_certificates(compiled_certificates, label_chunk_certificates)
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
    certificate_tuple = group_joined_init_multiref_certificates(
        tuple(compiled_certificates)
    )
    transition_specs = build_certificate_transition_specs(proof, certificate_tuple)
    coverage_plan = build_exact_node_coverage_plan(ir, transition_specs)
    external_pre_facts = frozenset(closed_init_facts)
    dependency_plan = None
    atomic_schedule = None
    if not frontiers and not layouts and not unresolved_side_conditions:
        dependency_plan = build_transition_dependency_plan(
            transition_specs, external_pre_facts=external_pre_facts
        )
        atomic_schedule = build_atomic_schedule(
            ir, transition_specs, external_pre_facts=external_pre_facts
        )
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
