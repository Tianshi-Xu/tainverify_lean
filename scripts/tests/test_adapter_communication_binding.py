"""Literal adapter capture metadata must reach the existing proof pipeline."""
from dataclasses import fields, replace

import pytest

from scripts.tests.test_parallel_authority import topology
from scripts.tests.test_proof_compiler import _hidden_embedding_alltoall_ir
from trainverify.bridge_emitter import parser
from trainverify.bridge_emitter.model_authority import ModelAuthorityIR, TargetQuery, bind_parallel_authority, materialize_target_ir
from trainverify.bridge_emitter.model_compiler import compile_shared_proof_dag, compile_shared_relation_dag
from trainverify.bridge_emitter.proof_compiler import build_default_registry

SOURCE = '''def pmAdapterCommunications : List (Nat × Nat × String × List Nat × List (Nat × Nat)) :=
[(0, 401, "AllToAllPrim", [0, 1], [(0, 301), (1, 302)]),
 (1, 402, "AllToAllPrim", [0, 1], [(0, 301), (1, 302)])]
'''


def model_from_ir(ir):
    query = {f.name: getattr(ir, f.name) for f in fields(TargetQuery) if hasattr(ir, f.name)}
    query.update(goal_id=ir.n, public_statement_digest="synthetic-adapter-fixture", prereqs=tuple(ir.prereqs))
    payload = {f.name: getattr(ir, f.name) for f in fields(ModelAuthorityIR) if hasattr(ir, f.name)}
    return ModelAuthorityIR(**payload, model_id="adapter-tracer", root=__file__,
                            targets={ir.n: TargetQuery(**query)}, aggregate=None)


def test_literal_adapter_capture_metadata_reaches_shared_proof_planning():
    assert hasattr(parser, "parse_adapter_communications"), "adapter communication capture is discarded by the Lean parser"
    records = parser.parse_adapter_communications(SOURCE, "pmAdapterCommunications")
    assert records[0].ranks == (0, 1)
    assert records[0].inputs == ((0, 301), (1, 302))
    ir = _hidden_embedding_alltoall_ir()
    ir.pm_adapter_communications = records
    model = bind_parallel_authority(model_from_ir(ir), topology(2, 2, 2, 2), graph_scope="plan")
    projected = materialize_target_ir(model, ir.n)
    assert projected.pm_adapter_communications == records
    proof = compile_shared_proof_dag(model, build_default_registry())
    assert proof.plans[ir.n].supported
    relation = compile_shared_relation_dag(model, proof)
    assert relation.projections[ir.n].terminal_fact_key is not None


def test_actual_exporter_wire_roundtrips_into_the_shared_compiler():
    from Verdict import graph_to_lean as exporter
    from Verdict.tests.test_adapter_communication_authority import SyntheticGraph, Tensor
    rows = []
    for rank in (0, 1):
        graph = SyntheticGraph(ranks=(0, 1), inputs=[Tensor(0, 301), Tensor(1, 302)], outputs=[Tensor(rank, 401 + rank)])
        graph.node.rank = rank
        graph.node.op = "OpName.AllToAllPrim"
        rows.extend(exporter.derive_adapter_communications(graph, graph.nodes))
    source = "def pmAdapterCommunications : List (Nat × Nat × String × List Nat × List (Nat × Nat)) := " + exporter._lean_adapter_communications(rows)
    ir = _hidden_embedding_alltoall_ir()
    ir.pm_adapter_communications = parser.parse_adapter_communications(source, "pmAdapterCommunications")
    model = bind_parallel_authority(model_from_ir(ir), topology(2, 2, 2, 2), graph_scope="plan")
    assert model.pm_replica_groups == ()  # Adapter communication is not logical replication.
    dag = compile_shared_relation_dag(model, compile_shared_proof_dag(model, build_default_registry()))
    assert dag.projections[ir.n].terminal_fact_key is not None


def test_loader_uses_metadata_of_the_actual_graph_scope(monkeypatch, tmp_path):
    from pathlib import Path
    fixture = Path(__file__).with_name("fixtures") / "CPKAttentionFW.lean"
    text = fixture.read_text().split("theorem publicInputs :", 1)[0] + "end CPKAttention\n"
    text = text.replace("smGraph", "smScoped").replace("pmGraph", "pmScoped")
    text = text.replace("exitGoal", "goal_7").replace("exitStatement", "goal_7_stmt")
    text = text.replace("smShapes", "smScopedInitShapes").replace("pmShapes", "pmScopedInitShapes")
    ty = "List (Nat × Nat × String × List Nat × List (Nat × Nat))"
    metadata = (SOURCE + f"def smScopedAdapterCommunications : {ty} := []\n"
                f"def pmScopedAdapterCommunications : {ty} := []\n"
                "def metadataSentinel : Nat := 0\n")
    text = text.replace("end CPKAttention\n", metadata + "end CPKAttention\n", 1)
    (tmp_path / "GeneratedData.lean").write_text(text)
    monkeypatch.setattr(parser, "DENOTE_DIR", "")
    monkeypatch.setattr(parser, "GEN_DIR", "")
    monkeypatch.setattr(parser, "GEN_FILE", "GeneratedData.lean")
    monkeypatch.setattr(parser, "MOD_PREFIX", "Fixture")
    ir = parser.load_goal_ir(7, str(tmp_path))
    assert ir.pm_graph_ref.endswith("pmScoped")
    assert ir.sm_adapter_communications == ()
    assert ir.pm_adapter_communications == ()


def test_real_fixture_loader_reaches_production_whole_model_builder(tmp_path, monkeypatch):
    from scripts.tests.adapter_communication_witness import write_fixture
    from trainverify.bridge_emitter import emit2
    model = write_fixture(tmp_path)
    assert model.aggregate is not None
    assert model.pm_adapter_communications is not None
    assert model.targets[7].pm_adapter_communications is model.pm_adapter_communications
    for name, value in {"DENOTE_DIR": "Fixture", "GEN_DIR": "Fixture", "GEN_FILE": "GeneratedData.lean", "MOD_PREFIX": "Fixture"}.items():
        monkeypatch.setattr(parser, name, value)
    bundle = emit2._build_whole_model_bundle(
        (7,), root=str(tmp_path), model_id="adapter-fixture", namespace="AdapterProof",
        module_prefix="AdapterProof", aggregate_theorem_name="all_outputs",
        parallel_topology=topology(2, 2, 2, 2), parallel_graph_scope="plan",
    )
    source = bundle["Main.lean"].decode()
    assert "theorem all_outputs : AdapterFixture.all_goals_stmt_full" in source
    assert '"sm_adapters": []' in source
    assert '"primary_out_tid": 401' in source


def test_model_projection_cannot_drop_present_adapter_capture():
    ir = _hidden_embedding_alltoall_ir()
    ir.pm_adapter_communications = parser.parse_adapter_communications(SOURCE, "pmAdapterCommunications")
    model = model_from_ir(ir)
    query = replace(model.targets[ir.n], pm_adapter_communications=None)
    corrupt = replace(model, targets={ir.n: query})
    with pytest.raises(ValueError, match="adapter authority differs"):
        compile_shared_proof_dag(corrupt, build_default_registry())


def test_direct_projection_cannot_drop_present_adapter_capture():
    from trainverify.bridge_emitter.proof_compiler import compile_proof_plan
    ir = _hidden_embedding_alltoall_ir()
    ir.pm_adapter_communications = parser.parse_adapter_communications(SOURCE, "pmAdapterCommunications")
    model = model_from_ir(ir)
    corrupt = replace(model, targets={ir.n: replace(model.targets[ir.n], pm_adapter_communications=None)})
    with pytest.raises(ValueError, match="adapter authority differs"):
        projected = materialize_target_ir(corrupt, ir.n)
        compile_proof_plan(projected, build_default_registry())


def test_absent_adapter_fields_preserve_existing_topology_bound_identity():
    from dataclasses import make_dataclass
    from scripts.tests.test_cp_k_attention import attention_ir, attention_model
    from trainverify.bridge_emitter.model_compiler import _authority_digest
    model = bind_parallel_authority(attention_model(attention_ir(4)), topology(), graph_scope="plan")
    names = ("topology", "graph_scope", "rank_map", "communications", "evidence_kind")
    legacy_type = make_dataclass("LegacyParallelGraphAuthority", [(name, object) for name in names], frozen=True)
    legacy = legacy_type(*(getattr(model.parallel_authority, name) for name in names))
    assert _authority_digest(model) == _authority_digest(replace(model, parallel_authority=legacy))


def test_sm_adapter_snapshot_cannot_silently_upgrade_absence_to_complete():
    from scripts.tests.test_cp_k_attention import attention_ir, attention_model
    from trainverify.bridge_emitter.parallel_authority import validate_graph_authority
    model = bind_parallel_authority(attention_model(attention_ir(4)), topology(), graph_scope="plan")
    altered = replace(model, sm_adapter_communications=())
    with pytest.raises(ValueError, match="adapter-binding-mismatch"):
        validate_graph_authority(altered, model.parallel_authority)


def test_absent_and_explicit_empty_authority_are_different():
    from trainverify.bridge_emitter.proof_compiler import compile_proof_plan
    assert parser.parse_adapter_communications("", "pmAdapterCommunications") is None
    empty = "def pmAdapterCommunications : List Nat := []"
    ir = _hidden_embedding_alltoall_ir()
    ir.pm_adapter_communications = parser.parse_adapter_communications(empty, "pmAdapterCommunications")
    assert ir.pm_adapter_communications == ()
    with pytest.raises(ValueError, match="inventory"):
        compile_proof_plan(ir, build_default_registry())


def test_coordinated_input_tid_swap_is_rejected_by_actual_writer_ownership():
    from trainverify.bridge_emitter.proof_compiler import compile_proof_plan
    ir = _hidden_embedding_alltoall_ir()
    records = parser.parse_adapter_communications(SOURCE, "pmAdapterCommunications")
    ir.pm_adapter_communications = tuple(replace(r, inputs=((0, 302), (1, 301))) for r in records)
    ir.pm_nodes = [replace(n, ins=[302, 301]) if n.op == "AllToAllPrim" else n for n in ir.pm_nodes]
    with pytest.raises(ValueError, match="input ownership mismatch"):
        compile_proof_plan(ir, build_default_registry())


@pytest.mark.parametrize("text", [SOURCE.replace('[0, 1]', '[0, True]'), SOURCE.replace('401', '-1'),
    SOURCE.replace('[(0, 301), (1, 302)]', '[(0, 301), (1, 302, 9)]'),
    SOURCE.replace('[0, 1]', 'list(range(2))')])
def test_malformed_or_executable_adapter_literals_are_rejected(text):
    with pytest.raises(ValueError):
        parser.parse_adapter_communications(text, "pmAdapterCommunications")
