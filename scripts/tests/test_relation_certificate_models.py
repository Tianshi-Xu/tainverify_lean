import ast
import dataclasses
import inspect

import pytest


def test_kv_certificate_models_are_frozen_leaf_dataclasses_with_stable_fields():
    from trainverify.bridge_emitter.relation_certificate_models import (
        KVRelationStepCertificate,
        ZigzagAttentionKVRelationCertificate,
    )

    assert tuple(field.name for field in dataclasses.fields(KVRelationStepCertificate)) == (
        "rule_id",
        "output_step_triple",
        "input_step_triple",
        "lean_theorem",
    )
    assert tuple(
        field.name for field in dataclasses.fields(ZigzagAttentionKVRelationCertificate)
    ) == (
        "rule_id",
        "role",
        "relation_kind",
        "output_step_triple",
        "input_step_triple",
        "steps",
    )
    step = KVRelationStepCertificate(
        "to-identity",
        ("sm:1:0", "pm:1:0", "pm:2:0"),
        ("sm:0:0", "pm:0:0", "pm:3:0"),
        "TrainVerify.Denote.example",
    )
    chain = ZigzagAttentionKVRelationCertificate(
        "zigzag-attention-k-ordinary-input-chain",
        "k",
        "ordinary",
        step.output_step_triple,
        step.input_step_triple,
        (step,),
    )
    with pytest.raises(dataclasses.FrozenInstanceError):
        step.rule_id = "mutated"
    assert chain.steps == (step,)


def test_pipeline_certificate_models_are_frozen_leaf_dataclasses_with_stable_fields():
    from trainverify.bridge_emitter.relation_certificate_models import (
        ChunkReconstructionCertificate,
        RMSNormRelationCertificate,
        RouterInputCheckpointCertificate,
    )

    expected = {
        ChunkReconstructionCertificate: (
            "rule_id", "input_relation_kind", "output_step_triple",
            "sm_full_step", "pm_full_source_step", "shard_rows", "width",
            "lean_theorem",
        ),
        RouterInputCheckpointCertificate: (
            "rule_id", "input_relation_kind", "equality_steps", "wrapper_ops",
            "previous_relation_step_triple",
        ),
        RMSNormRelationCertificate: (
            "rule_id", "input_relation_kind", "exposed_output_step_triple",
            "operator_step_triple", "input_step_triple", "shared_weight_tid",
            "lean_theorem",
        ),
    }
    for model, fields in expected.items():
        assert tuple(field.name for field in dataclasses.fields(model)) == fields
        assert model.__dataclass_params__.frozen is True


def test_unary_add_certificate_models_are_frozen_leaf_dataclasses_with_stable_fields():
    from trainverify.bridge_emitter.relation_certificate_models import (
        AddRelationCertificate,
        UnaryRelationCertificate,
        UnaryRelationChainCertificate,
    )

    expected = {
        UnaryRelationCertificate: (
            "rule_id", "input_relation_kind", "output_step_triple",
            "input_step_triple", "full_input_shape", "piece_input_shape",
            "full_output_shape", "piece_output_shape", "lean_theorem",
        ),
        UnaryRelationChainCertificate: (
            "rule_id", "input_relation_kind", "output_step_triple",
            "input_step_triple", "steps",
        ),
        AddRelationCertificate: (
            "rule_id", "input_relation_kind", "output_step_triple",
            "input_relation_step_triples", "lean_theorem",
        ),
    }
    for model, fields in expected.items():
        assert tuple(field.name for field in dataclasses.fields(model)) == fields
        assert model.__dataclass_params__.frozen is True


def test_attention_certificate_model_is_a_frozen_leaf_with_stable_fields():
    from trainverify.bridge_emitter.relation_certificate_models import (
        AttentionRelationCertificate,
    )

    assert tuple(
        field.name for field in dataclasses.fields(AttentionRelationCertificate)
    ) == (
        "rule_id", "input_relation_kind", "output_step_triple", "input_roles",
        "input_layouts", "input_relation_step_triples", "metadata_tids",
        "parameters", "full_output_shape", "piece_output_shape", "lean_theorem",
    )
    assert AttentionRelationCertificate.__dataclass_params__.frozen is True


def test_zigzag_q_certificate_model_is_the_final_frozen_leaf_with_stable_fields():
    from trainverify.bridge_emitter.relation_certificate_models import (
        ZigzagQRelationCertificate,
    )

    assert tuple(
        field.name for field in dataclasses.fields(ZigzagQRelationCertificate)
    ) == (
        "rule_id", "input_relation_kind", "output_step_triple",
        "full_linear_step", "gathered_linear_step", "gather_step",
        "input_step_triple", "replicated_weight_tid", "lean_theorems",
    )
    assert ZigzagQRelationCertificate.__dataclass_params__.frozen is True


def test_relation_compiler_reexports_the_leaf_model_identities():
    from trainverify.bridge_emitter import relation_certificate_models, relation_compiler

    assert relation_compiler.KVRelationStepCertificate is (
        relation_certificate_models.KVRelationStepCertificate
    )
    assert relation_compiler.ZigzagAttentionKVRelationCertificate is (
        relation_certificate_models.ZigzagAttentionKVRelationCertificate
    )
    for name in (
        "ChunkReconstructionCertificate",
        "RouterInputCheckpointCertificate",
        "RMSNormRelationCertificate",
        "UnaryRelationCertificate",
        "UnaryRelationChainCertificate",
        "AddRelationCertificate",
        "AttentionRelationCertificate",
        "ZigzagQRelationCertificate",
    ):
        assert getattr(relation_compiler, name) is getattr(relation_certificate_models, name)
    source = inspect.getsource(relation_compiler)
    for name in (
        "KVRelationStepCertificate",
        "ZigzagAttentionKVRelationCertificate",
        "ChunkReconstructionCertificate",
        "RouterInputCheckpointCertificate",
        "RMSNormRelationCertificate",
        "UnaryRelationCertificate",
        "UnaryRelationChainCertificate",
        "AddRelationCertificate",
        "AttentionRelationCertificate",
        "ZigzagQRelationCertificate",
    ):
        assert f"class {name}" not in source


def test_relation_certificate_models_has_no_compiler_or_renderer_imports():
    from trainverify.bridge_emitter import relation_certificate_models

    tree = ast.parse(inspect.getsource(relation_certificate_models))
    imports = "\n".join(
        ast.unparse(node)
        for node in tree.body
        if isinstance(node, (ast.Import, ast.ImportFrom))
    )
    for forbidden in (
        "relation_compiler",
        "proof_compiler",
        "parser",
        "composer",
        "renderer",
    ):
        assert forbidden not in imports
