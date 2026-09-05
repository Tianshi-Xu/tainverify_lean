"""Leaf data models for relation certificates with no compiler dependencies."""
from __future__ import annotations

from dataclasses import dataclass


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


@dataclass(frozen=True)
class AddRelationCertificate:
    rule_id: str
    input_relation_kind: str
    output_step_triple: tuple[str, str, str]
    input_relation_step_triples: tuple[
        tuple[str, str, str], tuple[str, str, str]
    ]
    lean_theorem: str


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
