import inspect
from dataclasses import dataclass


@dataclass(frozen=True)
class FactStub:
    layout: str
    step_triple: tuple[str, ...]
    source_step_triples: tuple[tuple[str, ...], ...] = ()
    joined_pm_step: str | None = None


@dataclass(frozen=True)
class TransitionStub:
    pre_facts: tuple[FactStub, ...]
    post_facts: tuple[FactStub, ...]


def test_selector_keeps_only_unproduced_pure_init_facts_by_full_equality():
    from trainverify.bridge_emitter.external_pre_fact_selector import (
        select_unproduced_external_pre_facts,
    )

    external = FactStub("sharded", ("init:1", "init:2"))
    produced = FactStub("replicated", ("init:3",))
    same_triple_different_fact = FactStub("joined", produced.step_triple)
    graph_written = FactStub("sharded", ("init:4", "pm:9:0"))
    transitions = (
        TransitionStub(
            (external, produced, same_triple_different_fact, graph_written),
            (produced,),
        ),
        TransitionStub((external,), ()),
    )
    assert select_unproduced_external_pre_facts(transitions) == frozenset(
        {external, same_triple_different_fact}
    )


def test_production_callers_delegate_only_unproduced_external_selection():
    from trainverify.bridge_emitter import model_compiler, relation_compiler

    relation_source = inspect.getsource(relation_compiler.compile_relation_plan)
    model_sources = (
        inspect.getsource(model_compiler._build_global_relation_plan)
        + inspect.getsource(model_compiler.materialize_target_relation_plan)
    )
    assert relation_source.count("select_unproduced_external_pre_facts") == 2
    assert model_sources.count("select_unproduced_external_pre_facts") == 2
    assert "fact not in produced_facts and _is_external_relation_fact" not in relation_source
    assert "fact not in produced and _is_external_relation_fact" not in model_sources
