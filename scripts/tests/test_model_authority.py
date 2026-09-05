import hashlib
import json
import re
import shutil
from dataclasses import replace
from pathlib import Path

import pytest

import trainverify.bridge_emitter.parser as parser_module
import trainverify.bridge_emitter.model_compiler as model_compiler_module
import trainverify.bridge_emitter.emit2 as emit2_module
from scripts.tests.real_goal_cache import compiled_goal
from trainverify.bridge_emitter.composer import (
    compose_shared_closed_bundle,
    render_closed_external_initial_state,
    render_closed_public_theorem,
    render_closed_segment,
    render_public_aggregate,
)
from trainverify.bridge_emitter.model_authority import (
    load_model_authority,
    materialize_target_ir,
)
from trainverify.bridge_emitter.model_compiler import (
    compile_shared_proof_dag,
    compile_shared_relation_dag,
    materialize_shared_prefix_relation_plan,
    materialize_terminal_projection_plan,
    materialize_target_relation_plan,
)
from trainverify.bridge_emitter.proof_compiler import (
    Diagnostic,
    DiagnosticCode,
    build_default_registry,
    compile_proof_plan,
)
from trainverify.bridge_emitter.relation_compiler import (
    KRankSumProducerCertificate,
    compile_relation_plan,
)


def _configure_gpt(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote/gpt_ly4_regen")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.gpt_ly4_regen")


def _configure_yoco(monkeypatch):
    monkeypatch.setattr(parser_module, "DENOTE_DIR", "trainverify/denote/yoco_goals")
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCOMoE.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.yoco_goals")


def _compiled_goal(goal_id: int, root: str):
    return compiled_goal(goal_id, root)


def test_model_authority_parses_graph_once_and_materializes_target_views(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    calls = 0
    scope_calls = 0
    lineage_calls = 0
    original = parser_module.parse_nodes
    original_scope = parser_module._public_full_scope
    original_lineage = parser_module.parse_lineage_block

    def counted(block):
        nonlocal calls
        calls += 1
        return original(block)

    def counted_scope(*args, **kwargs):
        nonlocal scope_calls
        scope_calls += 1
        return original_scope(*args, **kwargs)

    def counted_lineage(*args, **kwargs):
        nonlocal lineage_calls
        lineage_calls += 1
        return original_lineage(*args, **kwargs)

    monkeypatch.setattr(parser_module, "parse_nodes", counted)
    monkeypatch.setattr(parser_module, "_public_full_scope", counted_scope)
    monkeypatch.setattr(parser_module, "parse_lineage_block", counted_lineage)
    model = load_model_authority(
        (2, 3, 48), str(root), model_id="gpt2", allow_partial=False
    )

    assert calls == 2
    assert scope_calls == 1
    assert lineage_calls <= 51
    assert tuple(model.targets) == (2, 3, 48)
    assert model.aggregate is not None
    assert model.aggregate.ordered_target_ids == (2, 3, 48)
    assert model.aggregate.form == "conjunction"
    goal2 = materialize_target_ir(model, 2)
    goal3 = materialize_target_ir(model, 3)
    goal48 = materialize_target_ir(model, 48)
    assert goal2.sm_nodes is goal3.sm_nodes is goal48.sm_nodes is model.sm_nodes
    assert goal2.pm_nodes is goal3.pm_nodes is goal48.pm_nodes is model.pm_nodes
    assert (len(model.sm_nodes), len(model.pm_nodes)) == (236, 1565)
    assert goal2.lineage == parser_module.load_goal_ir(2, str(root)).lineage
    assert goal3.lineage == parser_module.load_goal_ir(3, str(root)).lineage
    assert goal48.public_statement_ref == parser_module.load_goal_ir(48, str(root)).public_statement_ref


def test_yoco3b_generated_only_authority_uses_exact_caller_certified_inventory(monkeypatch):
    monkeypatch.setattr(
        parser_module, "DENOTE_DIR", "trainverify/denote/yoco3b_heldout"
    )
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCO3B.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.yoco3b_heldout")
    root = Path(__file__).resolve().parents[2]

    model = load_model_authority(
        (1, 2, 3, 4, 5), str(root), model_id="yoco-3b", allow_partial=False
    )

    assert model.aggregate is not None
    assert model.aggregate.form == "conjunction"
    assert model.aggregate.ordered_target_ids == (1, 2, 3, 4, 5)
    goal1 = materialize_target_ir(model, 1)
    goal2 = materialize_target_ir(model, 2)
    assert goal1.public_statement_uses_contract_wrapper
    assert goal2.public_statement_uses_contract_wrapper
    assert goal1.tensor_value_bound_contracts[0].tid == 6281
    assert goal1.packed_cu_contracts[0].tid == 7804
    assert goal2.packed_cu_contracts[0].tid == 7804
    expected_value_ns = "TrainVerify.Denote.GeneratedYOCO3BHeldoutGoal2"
    assert goal1.sm_input_value_classes_ref == f"{expected_value_ns}.smInputValueClasses"
    assert goal1.pm_input_value_classes_ref == f"{expected_value_ns}.pmInputValueClasses"
    assert goal2.sm_input_value_classes_ref == f"{expected_value_ns}.smInputValueClasses"
    assert goal2.pm_input_value_classes_ref == f"{expected_value_ns}.pmInputValueClasses"


def test_yoco3b_shared_dual_ce_projection_is_one_atomic_fold(monkeypatch):
    monkeypatch.setattr(
        parser_module, "DENOTE_DIR", "trainverify/denote/yoco3b_heldout"
    )
    monkeypatch.setattr(parser_module, "GEN_DIR", "trainverify/denote")
    monkeypatch.setattr(parser_module, "GEN_FILE", "GeneratedYOCO3B.lean")
    monkeypatch.setattr(parser_module, "MOD_PREFIX", "denote.yoco3b_heldout")
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (1, 2, 3, 4, 5), str(root), model_id="yoco-3b", allow_partial=False
    )
    proof = compile_shared_proof_dag(model, build_default_registry())
    relation_dag = compile_shared_relation_dag(model, proof)
    relation = relation_dag.global_relation
    assert relation is not None

    source = render_closed_segment(
        materialize_target_ir(model, 1), relation, "segment_001123"
    )

    assert source.count("ClosedDepSegmentCertificate ") == 1
    assert source.count("let smFinal :=") == 1
    assert source.count("let pmFinal :=") == 1
    assert "fw_inner_chunk_ce_fst_allGather0_commute_2_of" in source
    assert "fw_inner_chunk_ce_snd_allGatherDim0_shards" in source

    goal2_relation = materialize_target_relation_plan(model, proof, relation_dag, 2)
    goal2_chain = goal2_relation.dependent_chain_plan
    assert goal2_chain is not None and goal2_chain.complete
    assert len(goal2_relation.transition_specs) == 2367
    assert not any(fact.kind == "label_bound" for fact in goal2_chain.authority_facts)
    assert len(goal2_chain.segments[-1].transition_ids) == 1
    assert goal2_chain.segments[-1].pm_range == (2969, 2973)
    shared_prefix = materialize_shared_prefix_relation_plan(
        model, proof, relation_dag, 1, 2
    )
    assert len(shared_prefix.transition_specs) == 2367
    assert len(shared_prefix.dependent_chain_plan.segments) == 1123
    assert shared_prefix.dependent_chain_plan.expected_sm_node_count == 1342
    assert shared_prefix.dependent_chain_plan.expected_pm_node_count == 2969
    assert shared_prefix.dependent_chain_plan.segments[-1].sm_range == (1341, 1342)
    assert shared_prefix.dependent_chain_plan.segments[-1].pm_range == (2967, 2969)
    assert not any(
        fact.kind == "label_bound"
        for fact in shared_prefix.dependent_chain_plan.authority_facts
    )
    goal2_terminal_ir, goal2_terminal = materialize_terminal_projection_plan(
        model, proof, relation_dag, shared_prefix, 2
    )
    terminal_source = render_closed_segment(
        goal2_terminal_ir, goal2_terminal, "segment_goal_2_terminal"
    )
    assert terminal_source.count("ClosedDepSegmentCertificate ") == 1
    assert terminal_source.count("let smFinal :=") == 1
    assert terminal_source.count("let pmFinal :=") == 1
    assert "fw_inner_chunk_ce_snd_allGatherDim0_shards" in terminal_source
    assert "fw_inner_chunk_ce_fst_allGather0_commute_2_of" not in terminal_source
    goal1_terminal_ir, goal1_terminal = materialize_terminal_projection_plan(
        model, proof, relation_dag, shared_prefix, 1
    )
    goal1_terminal_source = render_closed_segment(
        goal1_terminal_ir, goal1_terminal, "segment_goal_1_terminal"
    )
    assert goal1_terminal_source.count("ClosedDepSegmentCertificate ") == 1
    assert goal1_terminal_source.count("let pmFinal :=") == 1
    assert "fw_inner_chunk_ce_fst_allGather0_commute_2_of" in goal1_terminal_source
    assert 'outs := [6279], params := [0]' in goal1_terminal_source
    prefix_sources = {
        record.source: record.fact_id
        for record in shared_prefix.dependent_chain_plan.relation_facts
    }
    prefix_final_facts = set(shared_prefix.dependent_chain_plan.states[-1].fact_ids)
    for goal_id in (1, 2):
        projection = relation_dag.projections[goal_id]
        target = relation_dag.facts[projection.terminal_fact_key]
        terminal = [
            relation_dag.transitions[key] for key in projection.transition_keys
            if target in relation_dag.transitions[key].post_facts
        ]
        assert len(terminal) == 1
        for source in terminal[0].pre_facts:
            if source in prefix_sources:
                assert prefix_sources[source] in prefix_final_facts
    for goal_id in (3, 4, 5):
        projected = materialize_target_relation_plan(model, proof, relation_dag, goal_id)
        chain = projected.dependent_chain_plan
        assert chain is not None and chain.complete
        assert not any(
            fact.kind in {"packed_cu", "label_bound"}
            or (fact.kind == "tensor_eq" and fact.left_side == fact.right_side
                and fact.left_tid != fact.right_tid)
            for fact in chain.authority_facts
        )

    bundle = compose_shared_closed_bundle(
        model,
        relation_dag,
        "YOCO3BWhole",
        "denote.yoco3b_heldout.YOCO3BWhole",
        aggregate_theorem_name="yoco3b_all_goals",
    )
    assert "Target1Segment001123.lean" in bundle
    assert "Target2Segment001123.lean" in bundle
    assert "PrefixChain.lean" in bundle
    assert "Target3Public.lean" in bundle
    assert "Target4Public.lean" in bundle
    assert "Target5Public.lean" in bundle
    public = bundle["Public.lean"].decode()
    assert "YOCO3BWhole_goal_2_target_from_external_inputs" in public
    assert "TrainVerify.Denote.Generated.pmInputValueClasses" not in public
    assert "rw [YOCO3BWhole_chain_sm_nodes]" in public
    assert "rw [YOCO3BWhole_chain_pm_nodes]" in public
    assert "rw [segment_goal_1_terminal_sm_nodes_exact]" in public
    assert "rw [segment_goal_1_terminal_pm_nodes_exact]" in public
    assert "rw [segment_goal_2_terminal_sm_nodes_exact]" in public
    assert "rw [segment_goal_2_terminal_pm_nodes_exact]" in public
    assert "theorem segment_goal_1_terminal_sm_nodes_exact" in bundle["Target1Segment001123.lean"].decode()
    assert "theorem segment_goal_2_terminal_pm_nodes_exact" in bundle["Target2Segment001123.lean"].decode()
    assert "theorem authority_label_bound_pm_6281_holds_of_read" in bundle["Target1TerminalDefs.lean"].decode()
    assert "theorem authority_transition_eq_sm_7808_pm_7808_holds_of_read" in bundle["Target1TerminalDefs.lean"].decode()
    assert "apply authority_label_bound_pm_6281_holds_of_read" in public
    terminal_authority_declarations = [
        match.group(1)
        for path, source in bundle.items()
        if path.endswith("TerminalDefs.lean")
        for match in re.finditer(r"(?m)^def (authority_[A-Za-z0-9_]+)\s*:", source.decode())
    ]
    assert len(terminal_authority_declarations) == len(set(terminal_authority_declarations)), (
        "target terminal modules must not redeclare shared authority"
    )
    segment_paths = [
        path for path in bundle
        if re.fullmatch(r"(?:(?:Graph|Target)\d+)?Segment\d{6}\.lean", path)
    ]
    assert len(segment_paths) <= 1135, "target projections must reuse the shared segment prefix"


def test_model_authority_preserves_distinct_exact_target_graph_projections(monkeypatch):
    _configure_yoco(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (1, 2, 3, 4, 5), str(root), model_id="yoco-a04b", allow_partial=True
    )

    projections = [materialize_target_ir(model, goal_id) for goal_id in model.targets]
    assert [(item.n, len(item.sm_nodes), len(item.pm_nodes)) for item in projections] == [
        (1, 925, 2023),
        (2, 925, 2023),
        (3, 951, 2078),
        (4, 916, 2003),
        (5, 1, 4),
    ]
    assert projections[0].pm_graph_ref.endswith("sm_goal_1") is False
    assert projections[0].pm_graph_ref.endswith("pm_goal_1")
    assert projections[2].pm_graph_ref == "TrainVerify.Denote.Generated.pm"


def test_model_authority_binds_yoco_exact_full_statement_aggregate(monkeypatch):
    _configure_yoco(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (1, 2, 3, 4, 5), str(root), model_id="yoco-a04b"
    )
    assert model.aggregate.statement_ref == (
        "TrainVerify.Denote.GeneratedGoals.all_goals_stmt_full"
    )
    source = render_public_aggregate(model, "yoco_a04b_all_goals")
    assert "theorem yoco_a04b_all_goals" in source
    assert all(f"exact prove_goal_{goal_id}_closed" in source for goal_id in range(1, 6))


def test_shared_proof_dag_scopes_same_local_step_ids_from_distinct_graphs(monkeypatch):
    _configure_yoco(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (1, 2), str(root), model_id="yoco-a04b", allow_partial=True
    )
    shared = compile_shared_proof_dag(model, build_default_registry())

    assert tuple(shared.projections) == (1, 2)
    assert shared.projections[1].ancestry_steps != shared.projections[2].ancestry_steps
    assert len(shared.steps) == (
        len(shared.projections[1].ancestry_steps)
        + len(shared.projections[2].ancestry_steps)
    )


def test_shared_relation_dag_accepts_nontransition_composite_certificates(monkeypatch):
    _configure_yoco(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (4,), str(root), model_id="yoco-a04b", allow_partial=True
    )
    proof = compile_shared_proof_dag(model, build_default_registry())
    relation = compile_shared_relation_dag(model, proof)

    assert relation.projections[4].terminal_fact_key is not None
    assert len(relation.certificates) > len(relation.transition_certificate_keys)


def test_shared_relation_dag_scopes_local_facts_by_graph_authority(monkeypatch):
    _configure_yoco(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (1, 2), str(root), model_id="yoco-a04b", allow_partial=True
    )
    proof = compile_shared_proof_dag(model, build_default_registry())
    relation = compile_shared_relation_dag(model, proof)

    assert relation.projections[1].graph_authority_key != (
        relation.projections[2].graph_authority_key
    )
    assert relation.projections[1].terminal_fact_key != (
        relation.projections[2].terminal_fact_key
    )
    bundle = compose_shared_closed_bundle(
        model,
        relation,
        "YOCOTwoTargets",
        "denote.yoco_goals.YOCOTwoTargets",
    )
    assert list(bundle)[-1] == "Public.lean"
    assert any(path.startswith("Graph0") and path.endswith("Chain.lean") for path in bundle)
    assert any(path.startswith("Graph1") and path.endswith("Chain.lean") for path in bundle)
    public = bundle["Public.lean"].decode("utf-8")
    assert "theorem prove_goal_1_closed" in public
    assert "theorem prove_goal_2_closed" in public


def test_model_authority_binds_exact_public_aggregate(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(tuple(range(1, 313)), str(root), model_id="gpt2")

    aggregate = model.aggregate
    assert aggregate.statement_module == "denote.gpt_ly4_regen.GeneratedData"
    assert aggregate.statement_ref == "TrainVerify.Denote.Generated.all_goals_stmt"
    assert aggregate.goals_ref == "TrainVerify.Denote.Generated.goals"
    assert aggregate.goal_chunk_refs == tuple(
        f"TrainVerify.Denote.Generated.goalChunk_{n}" for n in range(1, 40)
    )
    assert aggregate.ordered_target_chunks == tuple(
        tuple(range(start, start + 8)) for start in range(1, 313, 8)
    )
    assert aggregate.ordered_target_ids == tuple(range(1, 313))
    assert aggregate.ordered_lineage_refs == tuple(
        f"TrainVerify.Denote.Generated.goal_{n}" for n in range(1, 313)
    )
    source = render_public_aggregate(model, "gpt_main_all_goals")
    assert (
        "theorem gpt_main_all_goals : "
        "TrainVerify.Denote.Generated.all_goals_stmt" in source
    )
    assert all(f"prove_goal_{n}_closed" in source for n in range(1, 313))
    assert source.count("goalChunk_") >= 39
    aggregate_refine = next(line for line in source.splitlines() if line.startswith("  refine "))
    assert aggregate_refine.count("⟨") == 38
    assert aggregate_refine.count("⟩") == 38
    assert aggregate_refine.startswith("  refine ⟨⟨")
    assert aggregate_refine.endswith("?_⟩")
    assert "goal_312_stmt" not in source


def test_model_authority_rejects_duplicate_or_empty_target_inventory(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    for targets, message in (((), "nonempty"), ((2, 2), "unique")):
        try:
            load_model_authority(targets, str(root), model_id="gpt2")
        except ValueError as exc:
            assert message in str(exc)
        else:
            raise AssertionError("invalid target inventory was accepted")


def test_model_authority_requires_complete_aggregate_unless_partial_is_explicit(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    strict = load_model_authority((2, 3, 48), str(root), model_id="gpt2")
    assert strict.aggregate is not None
    assert strict.aggregate.ordered_target_ids == (2, 3, 48)
    partial = load_model_authority(
        (2, 3, 48), str(root), model_id="gpt2", allow_partial=True
    )
    assert partial.aggregate is None


def test_whole_model_production_builder_uses_strict_authority_and_requires_main(monkeypatch):
    calls = {}
    model = object()
    proof = object()
    relation = object()

    def load(target_ids, root, *, model_id, allow_partial=False):
        calls["load"] = (target_ids, root, model_id, allow_partial)
        return model

    monkeypatch.setattr(emit2_module, "load_model_authority", load, raising=False)
    monkeypatch.setattr(
        emit2_module, "compile_shared_proof_dag",
        lambda actual, registry: proof if actual is model else None,
        raising=False,
    )
    monkeypatch.setattr(
        emit2_module, "compile_shared_relation_dag",
        lambda actual, actual_proof: relation
        if (actual is model and actual_proof is proof) else None,
        raising=False,
    )

    def compose(actual, actual_relation, namespace, module_prefix, *, aggregate_theorem_name):
        calls["compose"] = (
            actual, actual_relation, namespace, module_prefix, aggregate_theorem_name,
        )
        return {"Public.lean": b"public", "Main.lean": b"main"}

    monkeypatch.setattr(
        emit2_module, "compose_shared_closed_bundle", compose, raising=False
    )

    bundle = emit2_module._build_whole_model_bundle(
        (1, 2, 3, 4, 5),
        model_id="yoco-a04b",
        namespace="YOCOA04BWhole",
        module_prefix="denote.yoco_goals.YOCOA04BWhole",
        aggregate_theorem_name="yoco_a04b_all_goals",
        root="/authority",
    )

    assert calls["load"] == (
        (1, 2, 3, 4, 5), "/authority", "yoco-a04b", False,
    )
    assert calls["compose"] == (
        model, relation, "YOCOA04BWhole",
        "denote.yoco_goals.YOCOA04BWhole", "yoco_a04b_all_goals",
    )
    assert bundle["Main.lean"] == b"main"

    monkeypatch.setattr(
        emit2_module,
        "compose_shared_closed_bundle",
        lambda *args, **kwargs: {"Public.lean": b"partial"},
    )
    with pytest.raises(ValueError, match="Main.lean"):
        emit2_module._build_whole_model_bundle(
            (1,), model_id="broken", namespace="BrokenWhole",
            module_prefix="denote.BrokenWhole",
            aggregate_theorem_name="broken_all_goals", root="/authority",
        )


def test_emit2_whole_model_cli_uses_one_strict_bundle_and_publication(monkeypatch, tmp_path):
    output = tmp_path / "Whole"
    observed = {}

    def build(targets, **kwargs):
        observed["build"] = (targets, kwargs)
        return {"Public.lean": b"public", "Main.lean": b"main"}

    def publish(bundle, out_dir):
        observed["publish"] = (bundle, out_dir)

    monkeypatch.setattr(emit2_module, "_build_whole_model_bundle", build)
    monkeypatch.setattr(emit2_module, "_publish_closed_bundle", publish)
    monkeypatch.setattr(
        emit2_module.sys,
        "argv",
        [
            "emit2.py", "--whole-model", "--targets", "1-5",
            "--model-id", "yoco-a04b", "--namespace", "YOCOA04BWhole",
            "--module-prefix", "denote.yoco_goals.YOCOA04BWhole",
            "--aggregate-theorem", "yoco_a04b_all_goals",
            "--out", str(output), "--no-compile", "--quiet",
        ],
    )

    assert emit2_module.main() is None
    targets, kwargs = observed["build"]
    assert targets == (1, 2, 3, 4, 5)
    assert kwargs == {
        "model_id": "yoco-a04b",
        "namespace": "YOCOA04BWhole",
        "module_prefix": "denote.yoco_goals.YOCOA04BWhole",
        "aggregate_theorem_name": "yoco_a04b_all_goals",
        "root": emit2_module.REPO,
    }
    assert observed["publish"][1] == str(output)


def test_emit2_rejects_unchecked_canonical_whole_model_publication(monkeypatch, tmp_path):
    canonical = tmp_path / "canonical"
    published = []
    monkeypatch.setattr(
        emit2_module,
        "whole_model_artifact_path",
        lambda _model_id, _project_dir: canonical,
    )
    monkeypatch.setattr(
        emit2_module,
        "_build_whole_model_bundle",
        lambda *args, **kwargs: {"Public.lean": b"public", "Main.lean": b"main"},
    )
    monkeypatch.setattr(
        emit2_module,
        "_publish_closed_bundle",
        lambda *args, **kwargs: published.append((args, kwargs)),
    )
    monkeypatch.setattr(
        emit2_module.sys,
        "argv",
        [
            "emit2.py", "--whole-model", "--targets", "2,3,48",
            "--model-id", "gpt2", "--namespace", "GPT2Whole",
            "--module-prefix", "denote.gpt_ly4_regen.GPT2Whole",
            "--aggregate-theorem", "gpt2_all_goals",
            "--no-compile", "--quiet",
        ],
    )

    with pytest.raises(SystemExit) as stopped:
        emit2_module.main()

    assert stopped.value.code == 1
    assert published == []


def test_emit2_rejects_supported_model_alias_into_other_canonical_path(
    monkeypatch, tmp_path
):
    published = []
    monkeypatch.setattr(emit2_module, "TV", str(tmp_path))
    monkeypatch.setattr(
        emit2_module,
        "_build_whole_model_bundle",
        lambda *args, **kwargs: {"Public.lean": b"public", "Main.lean": b"main"},
    )
    monkeypatch.setattr(
        emit2_module,
        "_publish_closed_bundle",
        lambda *args, **kwargs: published.append((args, kwargs)),
    )
    other_model_path = emit2_module.whole_model_artifact_path("gpt2", tmp_path)
    monkeypatch.setattr(
        emit2_module.sys,
        "argv",
        [
            "emit2.py", "--whole-model", "--targets", "1-5",
            "--model-id", "yoco-a04b", "--namespace", "YOCOA04BWhole",
            "--module-prefix", "denote.yoco_goals.YOCOA04BWhole",
            "--aggregate-theorem", "yoco_a04b_all_goals",
            "--out", str(other_model_path), "--no-compile", "--quiet",
        ],
    )

    with pytest.raises(SystemExit) as stopped:
        emit2_module.main()

    assert stopped.value.code == 1
    assert published == []


def test_emit2_canonical_whole_model_uses_enclosing_atomic_transaction(
    monkeypatch, tmp_path
):
    canonical = tmp_path / "canonical"
    observed = []
    bundle = {"Public.lean": b"public", "Main.lean": b"main"}
    monkeypatch.setattr(
        emit2_module,
        "whole_model_artifact_path",
        lambda _model_id, _project_dir: canonical,
    )
    monkeypatch.setattr(
        emit2_module, "_build_whole_model_bundle", lambda *args, **kwargs: bundle
    )
    monkeypatch.setattr(
        emit2_module,
        "_compile_and_publish_canonical_whole_model",
        lambda *args, **kwargs: observed.append((args, kwargs)),
    )
    monkeypatch.setattr(
        emit2_module,
        "_compile_and_publish_closed_bundle",
        lambda *args, **kwargs: pytest.fail("canonical path used model-only publication"),
    )
    monkeypatch.setattr(
        emit2_module.sys,
        "argv",
        [
            "emit2.py", "--whole-model", "--targets", "2,3,48",
            "--model-id", "gpt2", "--namespace", "GPT2Whole",
            "--module-prefix", "denote.gpt_ly4_regen.GPT2Whole",
            "--aggregate-theorem", "gpt2_all_goals", "--quiet",
        ],
    )

    assert emit2_module.main() is None
    assert observed == [(
        (bundle, "gpt2", "denote.gpt_ly4_regen.GPT2Whole"),
        {
            "project_dir": emit2_module.TV,
            "axiom_targets": (
                "TrainVerify.Denote.GPT2Whole.gpt2_all_goals",
            ),
        },
    )]


def test_staged_bundle_rejects_existing_non_directory_before_publication(tmp_path):
    destination = tmp_path / "published"
    destination.write_text("old file\n")
    staged = tmp_path / ".published.staged-test"
    staged.mkdir()
    (staged / "value.txt").write_text("new\n")

    with pytest.raises(ValueError, match="real directory"):
        emit2_module._publish_staged_closed_bundle(staged, destination)

    assert destination.read_text() == "old file\n"
    assert (staged / "value.txt").read_text() == "new\n"


def test_staged_bundle_retirement_failure_keeps_new_snapshot_authoritative(
    monkeypatch, tmp_path
):
    destination = tmp_path / "published"
    destination.mkdir()
    (destination / "value.txt").write_text("old\n")
    staged = tmp_path / ".published.staged-test"
    staged.mkdir()
    (staged / "value.txt").write_text("new\n")
    original_rmtree = shutil.rmtree

    def fail_old_retirement(path, *args, **kwargs):
        if Path(path) == staged:
            raise OSError("retirement failed")
        return original_rmtree(path, *args, **kwargs)

    monkeypatch.setattr(shutil, "rmtree", fail_old_retirement)

    emit2_module._publish_staged_closed_bundle(staged, destination)

    assert (destination / "value.txt").read_text() == "new\n"
    assert (staged / "value.txt").read_text() == "old\n"


def test_whole_model_snapshot_recompiles_every_published_model_before_catalog(
    monkeypatch, tmp_path
):
    root = emit2_module.whole_model_artifact_root(tmp_path)
    expected = []
    for model_id, spec in emit2_module.SUPPORTED_WHOLE_MODEL_ARTIFACTS.items():
        publication = root.joinpath(*spec["module_prefix"].split("."))
        publication.mkdir(parents=True)
        (publication / "Main.lean").write_text(f"-- {model_id}\n")
        expected.append((spec["module_prefix"], publication))
    compiled = []
    audited = []
    monkeypatch.setattr(
        emit2_module,
        "_compile_closed_bundle_sources",
        lambda bundle, source, module, **kwargs: compiled.append(
            (module, Path(source), tuple(bundle))
        ) and None,
    )
    monkeypatch.setattr(
        emit2_module,
        "_audit_closed_bundle_axioms",
        lambda source, module, targets, **kwargs: audited.append(
            (module, Path(source), targets)
        ) and None,
    )

    assert emit2_module._compile_whole_model_snapshot_models(
        root, project_dir=tmp_path
    ) is None
    assert [(module, source) for module, source, _ in compiled] == expected
    assert all(paths == ("Main.lean",) for _, _, paths in compiled)
    assert audited == [
        (
            spec["module_prefix"],
            root.joinpath(*spec["module_prefix"].split(".")),
            (f"TrainVerify.Denote.{spec['namespace']}.{spec['aggregate_theorem']}",),
        )
        for spec in emit2_module.SUPPORTED_WHOLE_MODEL_ARTIFACTS.values()
    ]


def test_whole_model_snapshot_rejects_missing_internal_import_before_compile(
    monkeypatch, tmp_path
):
    root = emit2_module.whole_model_artifact_root(tmp_path)
    for model_id, spec in emit2_module.SUPPORTED_WHOLE_MODEL_ARTIFACTS.items():
        publication = root.joinpath(*spec["module_prefix"].split("."))
        publication.mkdir(parents=True)
        source = (
            f"import {spec['module_prefix']}.Missing\n"
            if model_id == "gpt2" else f"-- {model_id}\n"
        )
        (publication / "Main.lean").write_text(source)
    compile_calls = []
    monkeypatch.setattr(
        emit2_module,
        "_compile_closed_bundle_sources",
        lambda *args, **kwargs: compile_calls.append((args, kwargs)) or None,
    )

    failure = emit2_module._compile_whole_model_snapshot_models(
        root, project_dir=tmp_path
    )

    assert failure is not None
    assert failure[0] == "gpt2"
    assert "missing internal whole-model source" in failure[2]
    assert compile_calls == []


def test_canonical_whole_model_catalog_failure_preserves_enclosing_snapshot(
    monkeypatch, tmp_path
):
    root = emit2_module.whole_model_artifact_root(tmp_path)
    old_model = emit2_module.whole_model_artifact_path("gpt2", tmp_path)
    old_model.mkdir(parents=True)
    (old_model / "sentinel.lean").write_text("old model\n")
    (root / "Catalog").mkdir()
    (root / "Catalog" / "sentinel.lean").write_text("old catalog\n")
    bundle = {"Main.lean": b"new model\n"}

    monkeypatch.setattr(
        emit2_module, "_compile_whole_model_snapshot_models",
        lambda *args, **kwargs: None,
    )
    monkeypatch.setattr(
        emit2_module,
        "_compile_and_publish_whole_model_catalog",
        lambda *args, **kwargs: ("Catalog.lean", 1, "catalog rejected"),
    )

    failure = emit2_module._compile_and_publish_canonical_whole_model(
        bundle,
        "gpt2",
        "denote.gpt_ly4_regen.GPT2Whole",
        project_dir=tmp_path,
        axiom_targets=("TrainVerify.Denote.GPT2Whole.gpt2_all_goals",),
    )

    assert failure == ("Catalog.lean", 1, "catalog rejected")
    assert (old_model / "sentinel.lean").read_text() == "old model\n"
    assert (root / "Catalog" / "sentinel.lean").read_text() == "old catalog\n"
    assert not list(root.parent.glob(".whole-models.staged-*"))


def test_canonical_whole_model_publishes_model_and_catalog_as_one_snapshot(
    monkeypatch, tmp_path
):
    root = emit2_module.whole_model_artifact_root(tmp_path)
    old_model = emit2_module.whole_model_artifact_path("gpt2", tmp_path)
    old_model.mkdir(parents=True)
    (old_model / "sentinel.lean").write_text("old model\n")
    (root / "preserved").mkdir()
    (root / "preserved" / "keep.txt").write_text("keep\n")
    (root / "Catalog").mkdir()
    (root / "Catalog" / "sentinel.lean").write_text("old catalog\n")
    bundle = {"Main.lean": b"new model\n"}

    monkeypatch.setattr(
        emit2_module, "_compile_whole_model_snapshot_models",
        lambda *args, **kwargs: None,
    )

    def publish_catalog(candidate_root, **kwargs):
        catalog = Path(candidate_root) / "Catalog"
        shutil.rmtree(catalog)
        catalog.mkdir()
        (catalog / "Main.lean").write_text("new catalog\n")
        return None

    monkeypatch.setattr(
        emit2_module, "_compile_and_publish_whole_model_catalog", publish_catalog
    )

    failure = emit2_module._compile_and_publish_canonical_whole_model(
        bundle,
        "gpt2",
        "denote.gpt_ly4_regen.GPT2Whole",
        project_dir=tmp_path,
        axiom_targets=("TrainVerify.Denote.GPT2Whole.gpt2_all_goals",),
    )

    assert failure is None
    assert (old_model / "Main.lean").read_bytes() == bundle["Main.lean"]
    assert not (old_model / "sentinel.lean").exists()
    assert (root / "Catalog" / "Main.lean").read_text() == "new catalog\n"
    assert not (root / "Catalog" / "sentinel.lean").exists()
    assert (root / "preserved" / "keep.txt").read_text() == "keep\n"
    assert not list(root.parent.glob(".whole-models.staged-*"))


def test_canonical_transaction_locks_before_snapshot_capture_and_reuses_lock(
    monkeypatch, tmp_path
):
    root = emit2_module.whole_model_artifact_root(tmp_path)
    old_model = emit2_module.whole_model_artifact_path("gpt2", tmp_path)
    old_model.mkdir(parents=True)
    (old_model / "sentinel.lean").write_text("old model\n")
    (root / "Catalog").mkdir()
    bundle = {"Main.lean": b"new model\n"}
    monkeypatch.setattr(
        emit2_module, "_compile_whole_model_snapshot_models",
        lambda *args, **kwargs: None,
    )

    def publish_catalog(candidate_root, **kwargs):
        catalog = Path(candidate_root) / "Catalog"
        shutil.rmtree(catalog)
        catalog.mkdir()
        (catalog / "Main.lean").write_text("new catalog\n")
        return None

    monkeypatch.setattr(
        emit2_module, "_compile_and_publish_whole_model_catalog", publish_catalog
    )
    events = []
    real_flock = emit2_module.fcntl.flock
    real_copytree = shutil.copytree
    real_publish = emit2_module._publish_staged_closed_bundle

    def observed_flock(fd, operation):
        events.append(("lock", fd, operation))
        return real_flock(fd, operation)

    def observed_copytree(*args, **kwargs):
        events.append(("copy",))
        return real_copytree(*args, **kwargs)

    def observed_publish(staged, destination, **kwargs):
        if Path(destination) == root:
            events.append(("root-publish", kwargs.get("parent_fd")))
        return real_publish(staged, destination, **kwargs)

    monkeypatch.setattr(emit2_module.fcntl, "flock", observed_flock)
    monkeypatch.setattr(shutil, "copytree", observed_copytree)
    monkeypatch.setattr(
        emit2_module, "_publish_staged_closed_bundle", observed_publish
    )

    assert emit2_module._compile_and_publish_canonical_whole_model(
        bundle,
        "gpt2",
        "denote.gpt_ly4_regen.GPT2Whole",
        project_dir=tmp_path,
    ) is None
    assert events[0][0] == "lock"
    copy_index = next(i for i, event in enumerate(events) if event[0] == "copy")
    publish = next(event for event in events if event[0] == "root-publish")
    assert copy_index > 0
    assert publish[1] == events[0][1]


def test_canonical_retirement_failure_does_not_downgrade_committed_publication(
    monkeypatch, tmp_path
):
    root = emit2_module.whole_model_artifact_root(tmp_path)
    old_model = emit2_module.whole_model_artifact_path("gpt2", tmp_path)
    old_model.mkdir(parents=True)
    (old_model / "sentinel.lean").write_text("old model\n")
    (root / "Catalog").mkdir()
    bundle = {"Main.lean": b"new model\n"}
    monkeypatch.setattr(
        emit2_module, "_compile_whole_model_snapshot_models",
        lambda *args, **kwargs: None,
    )

    def publish_catalog(candidate_root, **kwargs):
        catalog = Path(candidate_root) / "Catalog"
        shutil.rmtree(catalog)
        catalog.mkdir()
        (catalog / "Main.lean").write_text("new catalog\n")
        return None

    monkeypatch.setattr(
        emit2_module, "_compile_and_publish_whole_model_catalog", publish_catalog
    )
    original_rmtree = shutil.rmtree

    def fail_retired_root(path, *args, **kwargs):
        candidate = Path(path)
        if candidate.name.startswith(".whole-models.staged-") and (
            candidate / "denote/gpt_ly4_regen/GPT2Whole/sentinel.lean"
        ).exists():
            raise OSError("retirement failed")
        return original_rmtree(path, *args, **kwargs)

    monkeypatch.setattr(shutil, "rmtree", fail_retired_root)

    assert emit2_module._compile_and_publish_canonical_whole_model(
        bundle,
        "gpt2",
        "denote.gpt_ly4_regen.GPT2Whole",
        project_dir=tmp_path,
    ) is None
    assert (old_model / "Main.lean").read_bytes() == b"new model\n"
    assert list(root.parent.glob(".whole-models.staged-*"))


def test_supported_whole_models_share_one_ignored_artifact_root(tmp_path):
    root = emit2_module.whole_model_artifact_root(tmp_path)
    assert root == tmp_path / ".artifacts" / "whole-models"
    assert {
        model_id: emit2_module.whole_model_artifact_path(model_id, tmp_path)
        .relative_to(root).as_posix()
        for model_id in emit2_module.SUPPORTED_WHOLE_MODEL_ARTIFACTS
    } == {
        "gpt2": "denote/gpt_ly4_regen/GPT2Whole",
        "yoco-a04b": "denote/yoco_goals/YOCOA04BWhole",
        "yoco-3b": "denote/yoco3b_heldout/YOCO3BWhole",
    }


def test_whole_model_catalog_binds_all_three_independent_publications(tmp_path):
    root = emit2_module.whole_model_artifact_root(tmp_path)
    for model_id in emit2_module.SUPPORTED_WHOLE_MODEL_ARTIFACTS:
        path = emit2_module.whole_model_artifact_path(model_id, tmp_path)
        path.mkdir(parents=True)
        (path / "Main.lean").write_text(f"-- {model_id}\n")
        (path / "Public.lean").write_text(f"-- {model_id} public\n")

    bundle = emit2_module._build_whole_model_catalog_bundle(root)
    manifest = json.loads(bundle["Manifest.json"])
    assert manifest["schema_version"] == 1
    assert manifest["composition"] == "isolated-model-entrypoints"
    assert [item["model_id"] for item in manifest["models"]] == [
        "gpt2", "yoco-a04b", "yoco-3b",
    ]
    assert [item["targets"] for item in manifest["models"]] == [
        [2, 3, 48], [1, 2, 3, 4, 5], [1, 2, 3, 4, 5],
    ]
    assert all(item["modules"] == 2 for item in manifest["models"])
    assert set(bundle) == {
        "GPT2.lean", "YOCOA04B.lean", "YOCO3B.lean", "Manifest.json",
    }
    assert "import denote.gpt_ly4_regen.GPT2Whole.Main" in bundle["GPT2.lean"].decode()
    assert (
        "theorem verified : TrainVerify.Denote.GeneratedGoals.all_goals_stmt_full := "
        "TrainVerify.Denote.GPT2Whole.gpt2_all_goals"
    ) in bundle["GPT2.lean"].decode()
    assert "import denote.yoco_goals.YOCOA04BWhole.Main" in bundle["YOCOA04B.lean"].decode()
    assert "import denote.yoco3b_heldout.YOCO3BWhole.Main" in bundle["YOCO3B.lean"].decode()
    assert "all_supported_models" not in "".join(
        payload.decode() for name, payload in bundle.items() if name.endswith(".lean")
    )

    (emit2_module.whole_model_artifact_path("gpt2", tmp_path) / "Main.lean").unlink()
    with pytest.raises(ValueError, match="missing Main.lean"):
        emit2_module._build_whole_model_catalog_bundle(root)


def test_whole_model_catalog_is_kernel_gated_and_published_atomically(monkeypatch, tmp_path):
    root = emit2_module.whole_model_artifact_root(tmp_path)
    for model_id in emit2_module.SUPPORTED_WHOLE_MODEL_ARTIFACTS:
        path = emit2_module.whole_model_artifact_path(model_id, tmp_path)
        path.mkdir(parents=True)
        (path / "Main.lean").write_text(f"-- {model_id}\n")
    observed = []

    def compile_bundle(
        bundle, stage, module_prefix, *, project_dir,
        compile_project_dependencies=True,
    ):
        observed.append((
            "compile", tuple(bundle), module_prefix, Path(project_dir),
            compile_project_dependencies,
        ))
        return None

    def audit(stage, module_prefix, targets, *, project_dir, imported_module=None):
        observed.append(("audit", imported_module, targets, Path(project_dir)))
        return None

    monkeypatch.setattr(emit2_module, "_compile_closed_bundle_sources", compile_bundle)
    monkeypatch.setattr(emit2_module, "_audit_closed_bundle_axioms", audit)
    assert emit2_module._compile_and_publish_whole_model_catalog(
        root, project_dir=tmp_path
    ) is None
    catalog = root / "Catalog"
    assert {path.name for path in catalog.iterdir()} == {
        "GPT2.lean", "YOCOA04B.lean", "YOCO3B.lean", "Manifest.json",
    }
    assert observed == [
        (
            "compile", ("GPT2.lean", "YOCOA04B.lean", "YOCO3B.lean"),
            "denote.WholeModels", tmp_path, False,
        ),
        (
            "audit", "denote.WholeModels.GPT2",
            ("TrainVerify.Denote.WholeModels.GPT2.verified",), tmp_path,
        ),
        (
            "audit", "denote.WholeModels.YOCOA04B",
            ("TrainVerify.Denote.WholeModels.YOCOA04B.verified",), tmp_path,
        ),
        (
            "audit", "denote.WholeModels.YOCO3B",
            ("TrainVerify.Denote.WholeModels.YOCO3B.verified",), tmp_path,
        ),
    ]

    sentinel = (catalog / "Manifest.json").read_bytes()
    monkeypatch.setattr(
        emit2_module, "_compile_closed_bundle_sources",
        lambda *args, **kwargs: ("Main.lean", 1, "RED"),
    )
    assert emit2_module._compile_and_publish_whole_model_catalog(
        root, project_dir=tmp_path
    ) == ("Main.lean", 1, "RED")
    assert (catalog / "Manifest.json").read_bytes() == sentinel


def test_whole_model_cli_defaults_supported_models_to_artifact_root(monkeypatch, tmp_path):
    observed = {}
    monkeypatch.setattr(emit2_module, "TV", str(tmp_path))
    monkeypatch.setattr(
        emit2_module, "_build_whole_model_bundle",
        lambda *args, **kwargs: {"Public.lean": b"public", "Main.lean": b"main"},
    )
    monkeypatch.setattr(
        emit2_module, "_compile_and_publish_canonical_whole_model",
        lambda bundle, model_id, module, **kwargs: observed.setdefault(
            "publication", (model_id, module, kwargs)
        ) and None,
    )
    monkeypatch.setattr(
        emit2_module.sys, "argv",
        [
            "emit2.py", "--whole-model", "--targets", "2,3,48",
            "--model-id", "gpt2", "--namespace", "GPT2Whole",
            "--module-prefix", "denote.gpt_ly4_regen.GPT2Whole",
            "--aggregate-theorem", "gpt2_all_goals", "--quiet",
        ],
    )
    assert emit2_module.main() is None
    assert observed["publication"] == (
        "gpt2",
        "denote.gpt_ly4_regen.GPT2Whole",
        {
            "project_dir": str(tmp_path),
            "axiom_targets": (
                "TrainVerify.Denote.GPT2Whole.gpt2_all_goals",
            ),
        },
    )


def test_shared_proof_dag_hash_cons_targets_without_duplicating_steps(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (2, 3, 48), str(root), model_id="gpt2", allow_partial=True
    )

    shared = compile_shared_proof_dag(model, build_default_registry())

    assert tuple(shared.projections) == (2, 3, 48)
    assert len(shared.steps) == len(shared.projections[48].ancestry_steps)
    assert set(shared.projections[2].ancestry_steps) <= set(shared.projections[48].ancestry_steps)
    assert set(shared.projections[3].ancestry_steps) <= set(shared.projections[48].ancestry_steps)
    assert set(shared.steps) == {
        step_id
        for projection in shared.projections.values()
        for step_id in projection.ancestry_steps
    }
    assert all(projection.diagnostics == () for projection in shared.projections.values())


def test_whole_model_authority_digest_binds_target_order_and_public_query(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (2, 3, 48), str(root), model_id="gpt2", allow_partial=True
    )
    baseline = model_compiler_module._authority_digest(model)

    query = model.targets[2]
    statement_path = root.joinpath(
        "trainverify", *query.public_statement_module.split(".")
    ).with_suffix(".lean")
    statement_text = statement_path.read_text()
    statement_name = query.public_statement_ref.rsplit(".", 1)[-1]
    statement_block = parser_module.extract_def_block(statement_text, statement_name)
    assert query.public_statement_digest == hashlib.sha256(
        statement_block.encode("utf-8")
    ).hexdigest()

    changed_targets = dict(model.targets)
    changed_targets[3] = replace(
        changed_targets[3],
        public_statement_ref=changed_targets[3].public_statement_ref + "_mutated",
    )
    assert model_compiler_module._authority_digest(
        replace(model, targets=changed_targets)
    ) != baseline
    reordered_targets = {n: model.targets[n] for n in (48, 2, 3)}
    assert model_compiler_module._authority_digest(
        replace(model, targets=reordered_targets)
    ) != baseline


def test_target_projection_digest_binds_certificate_step_payload(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (2,), str(root), model_id="gpt2", allow_partial=True
    )
    registry = build_default_registry()
    baseline = compile_shared_proof_dag(model, registry).projections[2].projection_digest
    original = model_compiler_module.compile_proof_plan

    def mutate_step(ir, rules):
        plan = original(ir, rules)
        changed = replace(plan.steps[0], rule_id=plan.steps[0].rule_id + "-mutated")
        return replace(plan, steps=(changed, *plan.steps[1:]))

    monkeypatch.setattr(model_compiler_module, "compile_proof_plan", mutate_step)
    changed = compile_shared_proof_dag(model, registry).projections[2].projection_digest
    assert changed != baseline


def test_shared_relation_dag_content_addresses_facts_certificates_and_transitions(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (2, 3, 48), str(root), model_id="gpt2", allow_partial=True
    )
    proof = compile_shared_proof_dag(model, build_default_registry())
    compile_calls = 0
    original_compile = model_compiler_module.compile_relation_plan

    def counted_compile(ir, plan):
        nonlocal compile_calls
        compile_calls += 1
        return original_compile(ir, plan)

    monkeypatch.setattr(model_compiler_module, "compile_relation_plan", counted_compile)

    relation = compile_shared_relation_dag(model, proof)

    assert compile_calls == 1
    assert tuple(relation.projections) == (2, 3, 48)
    assert relation.facts and relation.certificates and relation.transitions
    assert all(len(key) == 64 for key in relation.facts)
    assert all(len(key) == 64 for key in relation.certificates)
    assert all(len(key) == 64 for key in relation.transitions)
    assert set(relation.projections[2].transition_keys) <= set(relation.projections[48].transition_keys)
    assert set(relation.projections[3].transition_keys) <= set(relation.projections[48].transition_keys)
    assert all(not item.unresolved_frontiers for item in relation.projections.values())
    assert len(relation.closures) == 1
    closure_key = next(iter(relation.closures))
    assert all(item.closure_key == closure_key for item in relation.projections.values())
    assert relation.closures[closure_key].representative_goal_id == 48
    assert relation.closures[closure_key].relation.dependent_chain_plan.complete
    assert len(relation.transition_certificate_keys) == len(relation.transitions)
    assert set(relation.transition_certificate_keys) == set(relation.transitions)
    assert set(relation.transition_certificate_keys.values()) <= set(relation.certificates)
    assert all(item.terminal_fact_key in item.fact_keys for item in relation.projections.values())
    global_relation = relation.global_relation
    assert len(global_relation.transition_specs) == len(relation.transitions)
    assert global_relation.dependent_chain_plan.complete
    global_final_state = global_relation.dependent_chain_plan.states[-1]
    global_records = {
        item.source: item for item in global_relation.dependent_chain_plan.relation_facts
    }
    assert all(
        global_records[relation.facts[item.terminal_fact_key]].fact_id
        in global_final_state.fact_ids
        for item in relation.projections.values()
    )
    closure = relation.closures[closure_key].relation.dependent_chain_plan
    final_state_id = closure.segments[-1].post_state_id
    final_state = next(item for item in closure.states if item.state_id == final_state_id)
    closure_records = {item.source: item for item in closure.relation_facts}
    projection_sources = [render_closed_external_initial_state(
        materialize_target_ir(model, 48),
        relation.closures[closure_key].relation,
        "SharedProjection",
    )]
    for projection in relation.projections.values():
        terminal = relation.facts[projection.terminal_fact_key]
        assert closure_records[terminal].fact_id in final_state.fact_ids
        source = render_closed_public_theorem(
            materialize_target_ir(model, projection.goal_id),
            relation.closures[projection.closure_key].relation,
            "SharedProjection",
            explicit_target_source=terminal,
            declaration_prefix=f"SharedProjection_goal_{projection.goal_id}",
            include_external=False,
        )
        assert f"SharedProjection_goal_{projection.goal_id}_public_statement" in source
        projection_sources.append(source)
    combined = "\n".join(projection_sources)
    assert combined.count("private theorem SharedProjection_initial_state") == 1
    assert combined.count("theorem prove_goal_") == 3

    multi_closure_relation = replace(
        relation,
        closures={**relation.closures, "synthetic-second-maximal-closure": next(iter(relation.closures.values()))},
    )
    bundle = compose_shared_closed_bundle(
        model,
        multi_closure_relation,
        "SharedProjection",
        "denote.gpt_ly4_regen.SharedProjection",
    )
    assert "Chain.lean" in bundle
    assert list(bundle)[-1] == "Public.lean"
    assert list(bundle).index("Chain.lean") < list(bundle).index("Target2Public.lean")
    public = bundle["Public.lean"].decode("utf-8")
    assert public.count("private theorem SharedProjection_initial_state") == 1
    assert public.count("theorem prove_goal_") == 3
    assert all(f"theorem prove_goal_{n}_closed" in public for n in (2, 3, 48))


def test_gpt_goal1_sum_producer_derives_dim2_from_shapes(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir = parser_module.load_goal_ir(1, str(root))
    proof = compile_proof_plan(ir, build_default_registry())

    relation = compile_relation_plan(ir, proof)

    sums = [item for item in relation.certificates
            if type(item) is KRankSumProducerCertificate]
    assert sums
    assert {item.gather_dim for item in sums} == {2}
    assert all(item.full_shape == (1, 8, 128) for item in sums)
    assert all(item.shard_shape == (1, 8, 32) for item in sums)


def test_gpt_goal107_bw_embedding_vocab_shards_close_dim0_relation(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWEmbeddingVocabCertificate"]
    assert len(certs) == 1
    cert = certs[0]
    assert cert.rank_count == 4
    assert cert.gather_dim == 0
    assert cert.shard_shape == (32, 32)
    assert cert.full_shape == (128, 32)
    assert cert.ids_fact.layout == "sharded"
    assert cert.ids_fact.step_triple == ("init:714", "init:714")
    assert cert.lean_theorem == "TrainVerify.Denote.bw_embedding_eq_allGather_offset_4shards"
    add_certs = [item for item in relation.certificates
                 if type(item).__name__ == "KRankBWAddIdentityCertificate"]
    assert {item.lean_theorem for item in add_certs} <= {
        "TrainVerify.Denote.bw_add2_fst_same_shape",
        "TrainVerify.Denote.bw_add2_snd_same_shape",
    }
    assert add_certs
    assert all(item.operand_fact.layout == "sharded" for item in add_certs)
    assert all(item.operand_fact != item.input_fact for item in add_certs)
    transitions = {item.transition_id: item for item in relation.transition_specs}
    add_segments = [
        segment for segment in relation.dependent_chain_plan.segments
        if segment.transition_ids and all(
            transitions[tid].rule_id == "bw-add-identity-sharded-k-rank"
            for tid in segment.transition_ids
        )
    ]
    assert add_segments
    for segment in add_segments:
        state = next(item for item in relation.dependent_chain_plan.states
                     if item.state_id == segment.pre_state_id)
        for tid in segment.transition_ids:
            transition = transitions[tid]
            certificate = next(
                item for item in add_certs
                if item.output_fact == transition.post_facts[0]
            )
            operand = next(
                item for item in relation.dependent_chain_plan.relation_facts
                if item.source == certificate.operand_fact
            )
            assert operand.fact_id in state.fact_ids
    multiref = [item for item in relation.certificates
                if type(item).__name__ == "KRankBWMultirefSumCertificate"]
    assert {item.lean_theorem for item in multiref} == {
        "TrainVerify.Denote.tensorSum_pair_split_dim2_4_1_8_32",
        "TrainVerify.Denote.tensorSum_gather_dim1_4_1_2_32_g181",
        "TrainVerify.Denote.tensorSum_triple_gather_dim1_4_1_8_32_g114",
    }


def test_gpt_goal107_bw_layernorm_dx_dim1_certificates_advance_all_roots(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLayernormDxCertificate"]
    assert len(certs) == 9
    assert {item.gather_dim for item in certs} == {1}
    assert {item.rank_count for item in certs} == {4}
    by_step = {step.step_id: step for step in proof.steps}
    assert all(
        not frontier[0].startswith("init:")
        and by_step[frontier[0]].op != "BW_layernorm"
        for frontier in relation.unresolved_frontiers
    )


def test_gpt_goal107_bw_linear_dx_classifies_three_relation_families(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLinearDxCertificate"]
    assert len(certs) == 25
    assert {item.family for item in certs} == {
        "sequence-sharded", "column-sharded", "row-reduction"
    }
    assert sum(item.family == "sequence-sharded" for item in certs) == 7
    assert sum(item.family == "column-sharded" for item in certs) == 10
    assert sum(item.family == "row-reduction" for item in certs) == 8
    column = [item for item in certs if item.family == "column-sharded"]
    assert sum(item.lean_theorem.endswith("g276") for item in column) == 6
    assert sum(item.lean_theorem.endswith("g245") for item in column) == 2
    assert sum(item.lean_theorem.endswith("g213") for item in column) == 2
    by_step = {step.step_id: step for step in proof.steps}
    assert all(
        frontier[0].startswith("init:") or by_step[frontier[0]].op != "BW_linear"
        for frontier in relation.unresolved_frontiers
    )


def test_gpt_goal107_bw_gelu_uses_dynamic_axis_pointwise_relation(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWGeluCertificate"]
    assert len(certs) == 4
    assert [item.gather_dim for item in certs].count(1) == 3
    assert [item.gather_dim for item in certs].count(2) == 1
    assert {item.lean_theorem for item in certs} == {
        "TrainVerify.Denote.bw_gelu_allGatherPrimDimN_eq"
    }


def test_transpose_23_extra_theorems_respect_500k_heartbeat_budget():
    root = Path(__file__).resolve().parents[2]
    source = (root / "trainverify/denote/KRankTranspose23Extra.lean").read_text(
        encoding="utf-8"
    )
    for name in (
        "transposeAxes_2_3_allGather_dim3_to_dim2_rank4",
        "transposeAxes_2_3_allGather_dim1_rank4",
    ):
        budget = source.split(f"theorem {name}", 1)[0].rsplit(
            "set_option maxHeartbeats", 1
        )[1].split(" in", 1)[0].strip()
        assert int(budget) <= 500_000, name


def test_bw_linear_dx_column_theorem_respects_500k_heartbeat_budget():
    root = Path(__file__).resolve().parents[2]
    source = (root / "trainverify/denote/Denote.lean").read_text(encoding="utf-8")
    for name in (
        "bw_linear_dx_wsplit_dim1_4_g213",
        "bw_linear_dx_csplit_dim1_4_1_8_8_g245",
        "bw_linear_dx_csplit_dim1_4_1_8_8_g276",
    ):
        budget = source.split(f"theorem {name}", 1)[0].rsplit(
            "set_option maxHeartbeats", 1
        )[1].split(" in", 1)[0].strip()
        assert int(budget) <= 500_000, name


def test_bw_layernorm_dx_theorem_respects_500k_heartbeat_budget():
    root = Path(__file__).resolve().parents[2]
    source = (root / "trainverify/denote/Denote.lean").read_text(encoding="utf-8")
    theorem = source.split(
        "theorem bw_layernorm_dx_dp_split_dim1_4_1_2_32", 1
    )[0].rsplit("set_option maxHeartbeats", 1)[1].split(" in", 1)[0].strip()
    assert int(theorem) <= 500_000


def test_gpt_goal107_bw_sum_scalar_broadcast_preserves_dim2_sharding(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWSumCertificate"]
    assert len(certs) == 1
    assert certs[0].gather_dim == 2
    assert certs[0].gradient_fact.step_triple == ("init:896", "init:896")
    assert certs[0].lean_theorem == (
        "TrainVerify.Denote.bw_sum_allGatherPrimDimN_dim2_rank3"
    )


def test_gpt_goal107_bw_view_transports_joined_gradient_only(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "JoinedBWViewCertificate"]
    assert len(certs) == 16
    assert sum(
        item.input_shape == (1, 8, 4, 8) and item.target_shape == (1, 8, 32)
        for item in certs
    ) == 12
    assert sum(
        item.input_shape == (1, 8, 32) and item.target_shape == (1, 8, 4, 8)
        for item in certs
    ) == 4
    assert {item.lean_theorem for item in certs} == {
        "TrainVerify.Denote.RelationCompiler.JoinedRel.fw_view"
    }


def test_gpt_goal107_bw_transpose_reuses_axis_transport_certificates(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))
    by_step = {step.step_id: step for step in proof.steps}
    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankTransposeRelationCertificate"
             and by_step[item.sm_step_id].op == "BW_transpose"]
    assert len(certs) == 20
    assert {(item.input_gather_dim, item.output_gather_dim) for item in certs} == {
        (1, 1), (1, 2), (2, 1), (2, 3), (3, 2), (3, 3)
    }


def test_gpt_goal107_bw_matmul_classifies_six_semantic_layout_families(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWMatmulCertificate"]
    assert len(certs) == 16
    counts = {family: sum(item.family == family for item in certs) for family in {
        "fst-y-sharded", "snd-x-sharded", "snd-g-sharded",
        "batch-sharded", "fst-query-sharded", "fst-contraction-reduction",
        "snd-contraction-reduction",
    }}
    assert counts == {
        "fst-y-sharded": 2,
        "snd-x-sharded": 2,
        "snd-g-sharded": 2,
        "batch-sharded": 6,
        "fst-query-sharded": 1,
        "fst-contraction-reduction": 2,
        "snd-contraction-reduction": 1,
    }
    by_step = {step.step_id: step for step in proof.steps}
    assert all(
        frontier[0].startswith("init:") or by_step[frontier[0]].op != "BW_matmul"
        for frontier in relation.unresolved_frontiers
    )


def test_bw_matmul_segment213_theorems_respect_500k_heartbeat_budget():
    root = Path(__file__).resolve().parents[2]
    source = (root / "trainverify/denote/Denote.lean").read_text(encoding="utf-8")
    for theorem in (
        "bw_matmul_snd_split_1_4_8_8",
        "bw_matmul_fst_split_dW_1_4_8_8",
    ):
        prefix = source[:source.index(f"theorem {theorem}")]
        declaration = prefix.rsplit("set_option maxHeartbeats ", 1)[1]
        assert int(declaration.split()[0]) == 500000


def test_bw_softmax_dim1_helpers_respect_500k_heartbeat_budget():
    root = Path(__file__).resolve().parents[2]
    source = (root / "trainverify/denote/Denote.lean").read_text(encoding="utf-8")
    for theorem in (
        "softmaxBwdFromOutput_valAt_d8_g234",
        "softmaxBwdFromOutput_split_dim1_4_1_4_8_8_g234",
        "softmax_chunkPrimDimN_dim1_1_4_8_8_g234",
        "chunk1_gather1_roundtrip_1_1_8_8",
    ):
        prefix = source[:source.index(f"theorem {theorem}")]
        declaration = prefix.rsplit("set_option maxHeartbeats ", 1)[1]
        assert int(declaration.split()[0]) == 500000


def test_segment223_theorems_respect_500k_heartbeat_budget():
    root = Path(__file__).resolve().parents[2]
    source = (root / "trainverify/denote/Denote.lean").read_text(encoding="utf-8")
    for theorem in (
        "bw_linear_dx_dp_split_dim1_4_g169",
        "bw_matmul_snd_split_batchdim1_1_4_8_8",
    ):
        prefix = source[:source.index(f"theorem {theorem}")]
        declaration = prefix.rsplit("set_option maxHeartbeats ", 1)[1]
        assert int(declaration.split()[0]) == 500000


def test_gpt_goal107_bw_div_reuses_dynamic_sharded_div_certificate(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))
    by_step = {step.step_id: step for step in proof.steps}
    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankDivCertificate"
             and by_step[item.sm_step_id].op == "BW_div"]
    assert len(certs) == 4
    assert {item.gather_dim for item in certs} == {1, 2}
    assert {item.scalar_param for item in certs} == {2}


def test_gpt_goal107_bw_contiguous_reuses_identity_transport(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))
    by_step = {step.step_id: step for step in proof.steps}
    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankContiguousRelationCertificate"
             and by_step[item.sm_step_id].op == "BW_contiguous"]
    assert len(certs) == 4
    assert {item.gather_dim for item in certs} == {1, 2, 3}


def test_gpt_goal107_bw_softmax_closes_orthogonal_axis_shards(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(107, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWSoftmaxCertificate"]
    assert len(certs) == 4
    assert [item.gather_dim for item in certs].count(1) == 1
    assert [item.gather_dim for item in certs].count(2) == 3
    assert not relation.unresolved_frontiers


def test_gpt_goal109_cross_dp_wred_bw_embedding_sequence_reduction(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(109, str(root))

    cross = [item for item in relation.certificates
             if type(item).__name__ == "KRankAllReduceReconstructionCertificate"
             and item.rule_id == "cross-dp-wred-reconstruction-k-rank"]
    embedding = [item for item in relation.certificates
                 if type(item).__name__ == "KRankBWEmbeddingSequenceReductionCertificate"]
    sharded_ids = [item for item in relation.certificates
                   if type(item).__name__ == "KRankShardedIdsEmbeddingCertificate"]
    assert len(cross) == 1
    assert len(embedding) == 1
    assert len(sharded_ids) == 1
    assert embedding[0].ids_chunks_fact == sharded_ids[0].ids_chunks_fact
    assert embedding[0].gradient_fact.gather_dim == 1
    assert embedding[0].lean_theorem == (
        "TrainVerify.Denote.bw_embedding_seqchunk_4shards_1_8_32"
    )
    by_rule = {item.rule_id: item for item in relation.transition_specs}
    forward_transition = by_rule["embedding-sharded-ids-k-rank"]
    backward_transition = by_rule["bw-embedding-sequence-reduction-rank4"]
    assert sharded_ids[0].ids_chunks_fact in forward_transition.post_facts
    assert embedding[0].ids_chunks_fact in backward_transition.pre_facts
    by_step = {item.step_id: item for item in proof.steps}
    chunk_indices = {by_step[item].node_index for item in embedding[0].pm_chunk_steps}
    assert chunk_indices.isdisjoint(backward_transition.pm_node_indices)
    assert len(relation.dependent_chain_plan.segments) > 300
    backward_segment = next(
        item for item in relation.dependent_chain_plan.segments
        if item.transition_ids == (backward_transition.transition_id,)
    )
    source = render_closed_segment(ir, relation, backward_segment.segment_id)
    assert "bw_embedding_seqchunk_4shards_1_8_32" in source
    assert "ClosedDepSegmentCertificate" in source
    cross_transition = by_rule["cross-dp-wred-reconstruction-k-rank"]
    cross_segment = next(
        item for item in relation.dependent_chain_plan.segments
        if item.transition_ids == (cross_transition.transition_id,)
    )
    cross_source = render_closed_segment(ir, relation, cross_segment.segment_id)
    assert "cross_dp_wred_eq_allReducePrim" in cross_source
    assert "ClosedDepSegmentCertificate" in cross_source
    assert not relation.unresolved_frontiers


def test_gpt_goal112_bw_layernorm_dgamma_reduces_sequence_shards(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(112, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLayernormParamReductionCertificate"]
    assert len(certs) == 1
    assert certs[0].projection == ".2.1"
    assert certs[0].lean_theorem == (
        "TrainVerify.Denote.bw_layernorm_dw_dp_split_dim1_4_1_2_32"
    )
    assert not relation.unresolved_frontiers


def test_gpt_goal113_bw_layernorm_dbeta_reduces_sequence_shards(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(113, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLayernormParamReductionCertificate"]
    assert len(certs) == 1
    assert certs[0].projection == ".2.2"
    assert certs[0].lean_theorem == (
        "TrainVerify.Denote.bw_layernorm_db_dp_split_dim1_4_1_2_32"
    )
    assert not relation.unresolved_frontiers


def test_gpt_goal115_bw_linear_dw_reduces_sequence_shards(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir, proof, relation = _compiled_goal(115, str(root))

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLinearDwReductionCertificate"]
    assert len(certs) == 1
    assert certs[0].gradient_fact.gather_dim == 1
    assert certs[0].activation_fact.gather_dim == 1
    assert certs[0].lean_theorem == (
        "TrainVerify.Denote.bw_linear_dw_dp_split_dim1_4_1_2_32_g170"
    )
    assert not relation.unresolved_frontiers


def test_gpt_goal119_bw_linear_dw_shards_output_rows(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir = parser_module.load_goal_ir(119, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLinearDwShardedCertificate"]
    assert len(certs) == 1
    assert certs[0].output_fact.gather_dim == 0
    assert certs[0].lean_theorem == "TrainVerify.Denote.bw_linear_dw_split_dim2_4_g119"
    assert not relation.unresolved_frontiers


def test_gpt_goal179_bw_linear_dw_shards_wide_output_rows(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir = parser_module.load_goal_ir(179, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLinearDwShardedCertificate"]
    assert len(certs) == 1
    assert certs[0].lean_theorem == (
        "TrainVerify.Denote.bw_linear_dw_osplit_dim2_4_1_8_8_g179"
    )
    assert not relation.unresolved_frontiers


def test_gpt_goal150_bw_linear_dw_shards_input_columns(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir = parser_module.load_goal_ir(150, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLinearDwColumnShardedCertificate"]
    assert len(certs) == 1
    assert certs[0].output_fact.gather_dim == 1
    assert certs[0].lean_theorem == (
        "TrainVerify.Denote.bw_linear_dw_isplit_dim2_4_1_8_8_g154"
    )
    assert not relation.unresolved_frontiers


def test_gpt_goal214_bw_linear_dw_uses_direct_input_column_shards(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir = parser_module.load_goal_ir(214, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLinearDwColumnShardedCertificate"
             and item.output_fact.gather_dim == 1
             and item.lean_theorem.endswith("g214")]
    assert len(certs) == 1
    assert certs[0].lean_theorem == (
        "TrainVerify.Denote.bw_linear_dw_isplit_dim2_4_1_8_32_g214"
    )
    assert not relation.unresolved_frontiers


def test_gpt_goal144_bw_linear_dw_reduces_wide_sequence_shards(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    ir = parser_module.load_goal_ir(144, str(root))
    proof = compile_proof_plan(ir, build_default_registry())
    relation = compile_relation_plan(ir, proof)

    certs = [item for item in relation.certificates
             if type(item).__name__ == "KRankBWLinearDwReductionCertificate"]
    assert len(certs) == 1
    assert certs[0].lean_theorem == (
        "TrainVerify.Denote.bw_linear_dw_dp_chunk_both_dim1_4_1_8_32_128_g144"
    )
    assert not relation.unresolved_frontiers


def test_shared_proof_dag_rejects_an_unsupported_target(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (2, 3), str(root), model_id="gpt2", allow_partial=True
    )
    original = model_compiler_module.compile_proof_plan

    def fail_goal3(ir, registry):
        plan = original(ir, registry)
        if ir.n != 3:
            return plan
        diagnostic = Diagnostic(
            DiagnosticCode.UNSUPPORTED_OPERATOR, "sentinel unsupported target"
        )
        return replace(plan, diagnostics=(diagnostic,))

    monkeypatch.setattr(model_compiler_module, "compile_proof_plan", fail_goal3)
    with pytest.raises(ValueError, match="target 3.*unsupported"):
        compile_shared_proof_dag(model, build_default_registry())


def test_shared_relation_dag_rejects_unresolved_target_at_compile_boundary(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (2, 3), str(root), model_id="gpt2", allow_partial=True
    )
    proof = compile_shared_proof_dag(model, build_default_registry())
    original = model_compiler_module.compile_relation_plan

    def leave_goal3_unresolved(ir, plan):
        relation = original(ir, plan)
        if ir.n != 3:
            return relation
        return replace(
            relation,
            unresolved_frontiers=(("sentinel",),),
            unresolved_layouts=("ordinary",),
        )

    monkeypatch.setattr(
        model_compiler_module, "compile_relation_plan", leave_goal3_unresolved
    )
    with pytest.raises(ValueError, match="target 3.*unresolved"):
        compile_shared_relation_dag(model, proof)


def test_shared_relation_dag_localizes_target_failure(monkeypatch):
    _configure_gpt(monkeypatch)
    root = Path(__file__).resolve().parents[2]
    model = load_model_authority(
        (2, 3), str(root), model_id="gpt2", allow_partial=True
    )
    proof = compile_shared_proof_dag(model, build_default_registry())
    original = model_compiler_module.compile_relation_plan

    def fail_goal3(ir, plan):
        if ir.n == 3:
            raise RuntimeError("sentinel relation failure")
        return original(ir, plan)

    monkeypatch.setattr(model_compiler_module, "compile_relation_plan", fail_goal3)
    try:
        compile_shared_relation_dag(model, proof)
    except ValueError as exc:
        assert "target 3" in str(exc)
        assert "sentinel relation failure" in str(exc)
    else:
        raise AssertionError("target-local relation failure lost its context")
