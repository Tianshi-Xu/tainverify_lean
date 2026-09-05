import inspect
from dataclasses import dataclass


@dataclass(frozen=True)
class FactStub:
    step_triple: tuple[str, ...]
    source_step_triples: tuple[tuple[str, ...], ...] = ()
    joined_pm_step: str | None = None


def test_pure_init_authority_requires_every_materialized_reference_to_be_init():
    from trainverify.bridge_emitter.relation_authority_policy import (
        is_pure_init_relation_authority,
    )

    assert is_pure_init_relation_authority(
        FactStub(
            ("init:1", "init:2"),
            (("init:3", "init:4", "init:5"),),
            "init:6",
        )
    )
    assert not is_pure_init_relation_authority(FactStub(()))
    assert not is_pure_init_relation_authority(
        FactStub(("init:1",), (("init:2", "sm:9:0", "init:3"),))
    )
    assert not is_pure_init_relation_authority(
        FactStub(("init:1",), joined_pm_step="pm:7:0")
    )


def test_relation_compiler_compatibility_wrapper_delegates_without_old_policy():
    from trainverify.bridge_emitter import relation_compiler

    source = inspect.getsource(relation_compiler._is_external_relation_fact)
    assert "is_pure_init_relation_authority" in source
    assert "startswith" not in source
    assert relation_compiler._is_external_relation_fact(
        FactStub(("init:1", "init:2"))
    )
