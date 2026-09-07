"""Synthetic complete FW graph, not FreshGPT embedding or kernel acceptance.

Only authority input reads are in-memory; planner, segment, external and public
renderers all run for real. No Lean source/cache files or compiler outputs mocked.
"""
import hashlib
import io
import re
from dataclasses import fields, replace
from unittest.mock import patch

import pytest

from trainverify.bridge_emitter import composer, parser
from trainverify.bridge_emitter.model_authority import (
    ModelAuthorityIR, PublicAggregateAuthority, _query_from_ir,
)
from trainverify.bridge_emitter.model_compiler import (
    compile_shared_proof_dag, compile_shared_relation_dag,
)
from trainverify.bridge_emitter.proof_compiler import build_default_registry


def fixture(monkeypatch):
    ns = "TrainVerify.Denote.SyntheticShared"
    full, shard = [12, 2], [4, 2]
    initial = parser.LineageGoal(10, full, [(r, 100+r) for r in range(3)], [shard]*3, 0)
    ir = parser.GoalIR(
        n=1,
        sm_nodes=[parser.Node(0, "FW_contiguous", [10], [20], []),
                  parser.Node(0, "FW_contiguous", [20], [30], [])],
        pm_nodes=[parser.Node(r, op, [src+r], [dst+r], [])
                  for op, src, dst in (("FW_contiguous", 100, 200), ("FW_contiguous", 200, 300))
                  for r in range(3)],
        sm_shapes=[(10, full)], pm_shapes=[(100+r, shard) for r in range(3)],
        lineage=initial, prereqs=[10], sm_graph_ref=f"{ns}.sm", pm_graph_ref=f"{ns}.pm",
        sm_num_ranks=1, pm_num_ranks=3,
        public_statement_module="denote.SyntheticShared", init_goals_ref=f"{ns}.initGoals",
        public_statement_uses_contract_wrapper=False,
        init_lineages={10: initial}, full_init_goal_ids=(10,),
    )
    targets = {}
    source = [f"namespace {ns}",
              "def sm : GraphDecl := { numRanks := 1, nodes := [" + ", ".join(map(composer._node_text, ir.sm_nodes)) + "] }",
              "def pm : GraphDecl := { numRanks := 3, nodes := [" + ", ".join(map(composer._node_text, ir.pm_nodes)) + "] }",
              "def smInitEnv : ShapeEnv := shapeEnvOfList [(10, [12, 2])]",
              "def pmInitEnv : ShapeEnv := shapeEnvOfList [(100, [4, 2]), (101, [4, 2]), (102, [4, 2])]",
              "def initGoal_10 : LineageGoal := { ts := 10, tsShape := [12, 2], tps := [{rank := 0, tid := 100}, {rank := 1, tid := 101}, {rank := 2, tid := 102}], tpShapes := [[4, 2], [4, 2], [4, 2]], gatherDim := 0 }",
              "def initGoals : List LineageGoal := [initGoal_10]"]
    for goal_id, sm_tid, pm_base in ((1, 20, 200), (2, 30, 300)):
        lineage = parser.LineageGoal(sm_tid, full, [(r, pm_base+r) for r in range(3)], [shard]*3, 0)
        source += [f"def goal_{goal_id} : LineageGoal := {{ ts := {sm_tid}, tsShape := [12, 2], tps := [" +
                   ", ".join(f"{{ rank := {r}, tid := {pm_base+r} }}" for r in range(3)) +
                   "], tpShapes := [[4, 2], [4, 2], [4, 2]], gatherDim := 0 }",
                   f"def goal_{goal_id}_stmt : Prop := CoarseLineageHoldsWithInit sm pm goal_{goal_id} smInitEnv pmInitEnv initGoals"]
        target_ir = replace(ir, n=goal_id, lineage=lineage,
                            lineage_ref=f"{ns}.goal_{goal_id}",
                            public_statement_ref=f"{ns}.goal_{goal_id}_stmt")
        targets[goal_id] = _query_from_ir(target_ir, "")
    source += ["def all_goals_stmt : Prop := goal_2_stmt ∧ goal_1_stmt", f"end {ns}"]
    text = "\n".join(source) + "\n"
    for n, query in targets.items():
        block = parser.extract_def_block(text, f"goal_{n}_stmt")
        targets[n] = replace(query, public_statement_digest=hashlib.sha256(block.encode()).hexdigest())
    payload = {f.name: getattr(ir, f.name) for f in fields(ModelAuthorityIR) if hasattr(ir, f.name)}
    aggregate = PublicAggregateAuthority(
        "conjunction", ir.public_statement_module, f"{ns}.all_goals_stmt", "", "", (),
        ((2, 1),), (2, 1), (f"{ns}.goal_2_stmt", f"{ns}.goal_1_stmt"),
    )
    model = ModelAuthorityIR(**payload, model_id="synthetic-fw", root="/synthetic-input",
                             targets={n: targets[n] for n in (2, 1)}, aggregate=aggregate)
    inputs = {"/synthetic-input/trainverify/denote/SyntheticShared.lean": text}
    def read_input(path, *args, **kwargs):
        if str(path) not in inputs:
            raise FileNotFoundError(path)
        return io.StringIO(inputs[str(path)])
    monkeypatch.setattr(composer, "open", read_input, raising=False)
    proof = compile_shared_proof_dag(model, build_default_registry())
    dag = compile_shared_relation_dag(model, proof)
    assert dag.global_relation is not None
    assert dag.global_relation.dependent_chain_plan.complete
    assert len(dag.global_relation.dependent_chain_plan.segments) == 2
    return model, dag, inputs


def compose(model, dag):
    return composer.compose_shared_closed_bundle(
        model, dag, "Shared", "denote.SyntheticSharedProof", aggregate_theorem_name="all_closed",
    )


def test_generic_single_chain_real_renderers_and_byte_ledger(monkeypatch):
    model, dag, _ = fixture(monkeypatch)
    with patch.object(composer, "compose_closed_dependent_bundle", wraps=composer.compose_closed_dependent_bundle) as bundles, \
         patch.object(composer, "render_closed_external_initial_state", wraps=composer.render_closed_external_initial_state) as external, \
         patch.object(composer, "render_closed_public_theorem", wraps=composer.render_closed_public_theorem) as public:
        result = compose(model, dag)
    assert bundles.call_count == 1
    assert bundles.call_args.kwargs["include_public"] is False
    assert bundles.call_args.args[1] is dag.global_relation
    assert external.call_count == 1
    assert public.call_count == 2
    for call, projection in zip(public.call_args_list, dag.projections.values()):
        assert call.args[1] is dag.global_relation
        assert call.kwargs["explicit_target_source"] == dag.facts[projection.terminal_fact_key]
        assert call.kwargs["include_external"] is False
        assert call.kwargs["declaration_prefix"] == f"Shared_goal_{projection.goal_id}"
    assert not any(path.startswith(("Target", "Prefix", "Graph")) for path in result)
    assert list(result)[-3:] == ["Chain.lean", "Public.lean", "Main.lean"]
    ledger = {path: len(payload) for path, payload in result.items()}
    assert sum(bool(re.fullmatch(r"Segment\d{6}\.lean", path)) for path in ledger) == 2
    assert all(0 < size < 2_500_000 for size in ledger.values())
    emitted = result["Public.lean"].decode()
    assert emitted.count("private theorem Shared_initial_state") == 1
    assert emitted.count("faithful_closed_dep_chain_extract") == 2
    assert "import denote.FaithfulPlainBridge" in emitted
    for n, query in model.targets.items():
        assert f"theorem prove_goal_{n}_closed : {query.public_statement_ref}" in emitted
    main = result["Main.lean"].decode()
    assert main.index("exact prove_goal_2_closed") < main.index("exact prove_goal_1_closed")
    assert compose(model, dag) == result
    print("synthetic single-chain byte ledger:", ledger, "total", sum(ledger.values()))


@pytest.mark.parametrize("mutation", ["init_goals_ref", "sm_env", "pm_env", "contract_ref", "graph_ref", "local_init_ids"])
def test_incompatible_initial_contract_fails_before_composition(monkeypatch, mutation):
    model, dag, inputs = fixture(monkeypatch)
    query = model.targets[1]
    if mutation in {"sm_env", "pm_env"}:
        side = mutation[:2]
        path = next(iter(inputs))
        old = parser.extract_def_block(inputs[path], "goal_1_stmt")
        new = old.replace(f"{side}InitEnv", f"{side}LocalEnv")
        inputs[path] = inputs[path].replace(old, new).replace(
            "def goal_1 :", f"def {side}LocalEnv : ShapeEnv := {side}InitEnv\ndef goal_1 :"
        )
        query = replace(query, public_statement_digest=hashlib.sha256(new.encode()).hexdigest())
    elif mutation == "init_goals_ref":
        # The same Python IDs (and even a Lean alias) are not a supplied premise
        # equivalence proof. Distinct public source refs must fail closed.
        path = next(iter(inputs))
        old = parser.extract_def_block(inputs[path], "goal_1_stmt")
        new = old.replace("initGoals", "initGoalsLocal")
        inputs[path] = inputs[path].replace(old, new).replace(
            "def goal_1 :", "def initGoalsLocal : List LineageGoal := initGoals\ndef goal_1 :"
        )
        query = replace(query, init_goals_ref=query.init_goals_ref + "Local",
                        public_statement_digest=hashlib.sha256(new.encode()).hexdigest())
    elif mutation == "contract_ref":
        query = replace(query, public_statement_contract_ref="Different.localContract")
    elif mutation == "graph_ref":
        query = replace(query, pm_graph_ref="Different.pm")
    else:
        query = replace(query, full_init_goal_ids=())
    model = replace(model, targets={**model.targets, 1: query})
    with patch.object(composer, "compose_closed_dependent_bundle", wraps=composer.compose_closed_dependent_bundle) as bundles:
        with pytest.raises(ValueError, match=r"target 1.*initial contract.*(mismatch|unsupported)"):
            compose(model, dag)
        assert bundles.call_count == 0


def test_retained_target_missing_fails_closed(monkeypatch):
    model, dag, _ = fixture(monkeypatch)
    relation = dag.global_relation
    chain = relation.dependent_chain_plan
    terminal = dag.facts[dag.projections[1].terminal_fact_key]
    fact = next(f for f in chain.relation_facts if f.source == terminal)
    final = next(s for s in chain.states if s.state_id == chain.segments[-1].post_state_id)
    changed = replace(final, fact_ids=tuple(f for f in final.fact_ids if f != fact.fact_id))
    chain = replace(chain, states=tuple(changed if s == final else s for s in chain.states))
    dag = replace(dag, global_relation=replace(relation, dependent_chain_plan=chain))
    with pytest.raises(ValueError, match=r"target 1.*not retained.*final state"):
        compose(model, dag)


def test_wrong_projection_terminal_cannot_change_public_statement(monkeypatch):
    model, dag, _ = fixture(monkeypatch)
    projections = dict(dag.projections)
    projections[1] = replace(projections[1], terminal_fact_key=projections[2].terminal_fact_key)
    with pytest.raises(ValueError, match="terminal does not match public lineage"):
        compose(model, replace(dag, projections=projections))
