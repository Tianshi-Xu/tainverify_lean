"""Pure provenance policy for external closed-relation authority."""
from __future__ import annotations

from typing import Protocol


class RelationAuthorityView(Protocol):
    """Structural fields needed to classify one closed relation fact."""

    step_triple: tuple[str, ...]
    source_step_triples: tuple[tuple[str, ...], ...]
    joined_pm_step: str | None


def is_pure_init_relation_authority(fact: RelationAuthorityView) -> bool:
    """Return true only when every materialized reference is immutable InitGoal authority."""
    refs = [*fact.step_triple]
    refs.extend(ref for triple in fact.source_step_triples for ref in triple)
    if fact.joined_pm_step is not None:
        refs.append(fact.joined_pm_step)
    return bool(refs) and all(ref.startswith("init:") for ref in refs)
