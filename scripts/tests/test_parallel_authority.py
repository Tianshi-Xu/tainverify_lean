"""Configuration binding tests; these graph fixtures are not GPU captures."""
from dataclasses import replace

import pytest

from scripts.tests.test_cp_k_attention import attention_ir, attention_model
from trainverify.bridge_emitter import model_authority
from trainverify.bridge_emitter.model_compiler import compile_shared_proof_dag, compile_shared_relation_dag
from trainverify.bridge_emitter.proof_compiler import build_default_registry

PIN = "9a1be1d5fd1c063d80be82797692cdc7d23cfbef"


def topology(plan=4, runtime=8, cp=4, ep=2):
    """Synthetic, structurally valid source-topology record for unit tests."""
    from trainverify.parallel_topology import ParallelConfig, ParallelGroup, ParallelTopology
    groups = []
    for unit, start in enumerate(range(0, runtime, plan)):
        for role, size in (("scale_unit", plan), ("cp", cp), ("ep", ep)):
            for offset in range(0, plan, size):
                groups.append(ParallelGroup(role, unit, tuple(range(start + offset, start + offset + size))))
        for rank in range(cp):
            groups.append(ParallelGroup("data_lane", unit, tuple(range(start + rank, start + plan, cp))))
    eager = tuple(sorted({g.members for g in groups if len(g.members) > 1}))
    return ParallelTopology(ParallelConfig(plan, runtime, cp, ep, False, 8, runtime, 1), tuple(groups), eager, PIN)


def test_configuration_flows_through_model_projections_and_shared_dag():
    assert hasattr(model_authority, "bind_parallel_authority"), "configuration/topology is not connected to model authority"
    ir = attention_ir(4)
    model = attention_model(ir)
    bound = model_authority.bind_parallel_authority(model, topology(), graph_scope="plan", scale_unit=1)
    authority = bound.parallel_authority
    assert authority.rank_map == (4, 5, 6, 7)
    assert authority.topology.config.ep_size == 2
    for target in bound.targets:
        assert model_authority.materialize_target_ir(bound, target).parallel_authority is authority
    registry = build_default_registry()
    before = compile_shared_proof_dag(model, registry)
    proof = compile_shared_proof_dag(bound, registry)
    assert before.authority_digest != proof.authority_digest
    relations = compile_shared_relation_dag(bound, proof)
    assert len(relations.certificates) == 3
    assert relations.global_relation.dependent_chain_plan.complete


def test_rank_map_rejects_boolean_rank_even_when_equal_as_python_integer():
    from trainverify.bridge_emitter.parallel_authority import validate_graph_authority
    model = model_authority.bind_parallel_authority(attention_model(attention_ir(4)), topology(runtime=4), graph_scope="plan")
    from types import SimpleNamespace
    graph = SimpleNamespace(pm_nodes=[], pm_replica_groups=(), pm_num_ranks=4)
    corrupt = replace(model.parallel_authority, rank_map=(0, True, 2, 3), communications=())
    with pytest.raises(ValueError, match="invalid-rank-map"):
        validate_graph_authority(graph, corrupt)


def test_bound_target_cannot_substitute_a_different_shape_environment():
    model = model_authority.bind_parallel_authority(attention_model(attention_ir(4)), topology(), graph_scope="plan")
    queries = dict(model.targets)
    queries[0] = replace(queries[0], pm_shapes=list(reversed(queries[0].pm_shapes)))
    corrupt = replace(model, targets=queries)
    with pytest.raises(ValueError, match="target-graph-authority-mismatch"):
        compile_shared_proof_dag(corrupt, build_default_registry())


def test_single_target_public_aggregate_does_not_construct_a_tuple():
    from trainverify.bridge_emitter.composer import render_public_aggregate
    source = render_public_aggregate(public_attention_model(1), "all_outputs")
    assert "refine ⟨?_⟩" not in source
    assert "exact prove_goal_1_closed" in source


def public_attention_model(goal_id=0):
    """Use the existing exact CPKAttention declaration/public contract as input."""
    from trainverify.bridge_emitter.model_authority import PublicAggregateAuthority
    ir = attention_ir(3)
    for field, value in {
        "init_goals_ref": "initGoals", "lineage_ref": "exitGoal",
        "public_statement_ref": "exitStatement", "public_statement_contract_ref": "externalContract",
        "sm_input_value_classes_ref": "smInputValueClasses", "pm_input_value_classes_ref": "pmInputValueClasses",
    }.items():
        setattr(ir, field, "CPKAttention." + value)
    ir.public_statement_module = "CPKAttention"
    model = attention_model(ir)
    aggregate = PublicAggregateAuthority(
        "conjunction", "CPKAttention", "CPKAttention.exitStatement", "unit-fixture",
        "", (), ((goal_id,),), (goal_id,), ("CPKAttention.exitGoal",),
    )
    return replace(model, targets={goal_id: replace(model.targets[0], goal_id=goal_id)}, aggregate=aggregate)


def test_whole_model_builder_binds_configuration_before_planning(monkeypatch):
    import inspect
    from trainverify.bridge_emitter import emit2
    assert "parallel_topology" in inspect.signature(emit2._build_whole_model_bundle).parameters
    model = public_attention_model()
    monkeypatch.setattr(emit2, "load_model_authority", lambda *args, **kwargs: model)
    # Execute the real shared planners and renderer; no GPU source capture claim.
    bundle = emit2._build_whole_model_bundle(
        (0,), model_id="configuration-tracer", namespace="ParallelTracer",
        module_prefix="ParallelTracer", aggregate_theorem_name="all_outputs",
        parallel_topology=topology(3, 6, 3, 1), parallel_graph_scope="plan", parallel_scale_unit=1,
    )
    main = bundle["Main.lean"].decode()
    assert "source-checked-replica-group-projection" in main
    assert '"rank_map": [3, 4, 5]' in main
    assert "source-derived-topology" in main


def test_whole_model_cli_forwards_source_config_to_real_builder(monkeypatch, tmp_path):
    import json
    from trainverify import parallel_topology as api
    from trainverify.bridge_emitter import emit2
    config = tmp_path / "config.json"
    config.write_text(json.dumps({"plan_ngpus": 3, "runtime_ngpus": 6, "cp_size": 3, "ep_size": 1}))
    observed = {}
    def source(config, *, upstream_root, revision):
        observed.update(config=config, upstream_root=upstream_root, revision=revision)
        return topology(3, 6, 3, 1)
    # CLI plumbing isolation only. Actual pinned execution has its own probe.
    monkeypatch.setattr(api, "derive_topology", source)
    monkeypatch.setattr(emit2, "load_model_authority", lambda *args, **kwargs: public_attention_model(1))
    output = tmp_path / "ParallelTracer"
    monkeypatch.setattr(emit2.sys, "argv", [
        "emit2.py", "--whole-model", "--targets", "1", "--model-id", "configuration-tracer",
        "--namespace", "ParallelTracer", "--module-prefix", "ParallelTracer",
        "--aggregate-theorem", "all_outputs", "--out", str(output), "--no-compile",
        "--parallel-config", str(config), "--parallel-upstream-root", "/explicit/upstream",
        "--parallel-revision", PIN, "--parallel-graph-scope", "plan", "--parallel-scale-unit", "1",
    ])
    emit2.main()
    assert observed["upstream_root"] == "/explicit/upstream"
    assert observed["revision"] == PIN
    assert observed["config"].ep_size == 1
    assert '"rank_map": [3, 4, 5]' in (output / "Main.lean").read_text()


@pytest.mark.parametrize("cp,ep", [(2, 4), (1, 4)])
def test_same_plan_size_does_not_make_logical_replicas_a_cp_group(cp, ep):
    model = attention_model(attention_ir(4))
    with pytest.raises(ValueError, match="communication-group-mismatch"):
        model_authority.bind_parallel_authority(model, topology(4, 4, cp, ep), graph_scope="plan")


def test_correct_subgroup_authority_reports_missing_group_local_backend():
    from trainverify.bridge_emitter import parser
    ir = attention_ir(4)
    ir.pm_replica_groups = tuple(
        replace(group, cid=2 * group.cid + subgroup, members=group.members[2 * subgroup:2 * subgroup + 2])
        for group in ir.pm_replica_groups for subgroup in (0, 1)
    )
    for node in ir.pm_nodes:
        if node.op.endswith(("maybe_shuffle", "maybe_unshuffle")):
            node.params = [2, node.rank % 2]
    with pytest.raises(ValueError, match="unsupported-group-local-proof"):
        model_authority.bind_parallel_authority(attention_model(ir), topology(4, 4, 2, 4), graph_scope="plan")


def test_sliding_window_source_group_cannot_escape_topology_checks():
    ir = attention_ir(4)
    ir.pm_nodes = [replace(n, op="FW_attn_sliding_window") for n in ir.pm_nodes if n.op == "FW_attn_zigzag"]
    ir.pm_replica_groups = (ir.pm_replica_groups[1],)
    with pytest.raises(ValueError, match="communication-group-mismatch"):
        model_authority.bind_parallel_authority(attention_model(ir), topology(4, 4, 2, 4), graph_scope="plan")


def test_runtime_rank_cannot_replace_source_group_local_parameter():
    ir = attention_ir(4)
    for node in ir.pm_nodes:
        if node.op == "FW_maybe_shuffle":
            node.params = [4, 4 + node.rank]
    with pytest.raises(ValueError, match="source-rank-parameter-mismatch"):
        model_authority.bind_parallel_authority(attention_model(ir), topology(), graph_scope="plan", scale_unit=1)


def test_coherent_group_reordering_is_not_accepted_as_same_set():
    ir = attention_ir(4)
    ir.pm_replica_groups = tuple(replace(g, members=tuple(reversed(g.members))) for g in ir.pm_replica_groups)
    with pytest.raises(ValueError, match="communication-group-mismatch"):
        model_authority.bind_parallel_authority(attention_model(ir), topology(), graph_scope="plan")


def test_source_configuration_change_cannot_reuse_prior_shared_proof_authority():
    model = attention_model(attention_ir(4))
    first = model_authority.bind_parallel_authority(model, topology(), graph_scope="plan", scale_unit=0)
    second = model_authority.bind_parallel_authority(model, topology(), graph_scope="plan", scale_unit=1)
    proof = compile_shared_proof_dag(first, build_default_registry())
    with pytest.raises(ValueError, match="shared proof authority mismatch"):
        compile_shared_relation_dag(second, proof)


def test_direct_goal_planning_rechecks_attached_communication_bindings():
    from trainverify.bridge_emitter.proof_compiler import compile_proof_plan
    model = model_authority.bind_parallel_authority(attention_model(attention_ir(4)), topology(), graph_scope="plan")
    ir = model_authority.materialize_target_ir(model, 0)
    ir.parallel_authority = replace(ir.parallel_authority, communications=())
    with pytest.raises(ValueError, match="communication-binding-mismatch"):
        compile_proof_plan(ir, build_default_registry())
