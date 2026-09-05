"""Pure selection of unproduced immutable external relation facts."""
from __future__ import annotations

from collections.abc import Hashable, Iterable
from typing import Protocol

try:
    from .relation_authority_policy import is_pure_init_relation_authority
except ImportError:
    from relation_authority_policy import is_pure_init_relation_authority


class TransitionFactsView(Protocol):
    pre_facts: tuple[Hashable, ...]
    post_facts: tuple[Hashable, ...]


def select_unproduced_external_pre_facts(
    transitions: Iterable[TransitionFactsView],
) -> frozenset[Hashable]:
    """Select pure-init pre-facts with no equal transition-produced fact."""
    materialized = tuple(transitions)
    produced = {
        fact for transition in materialized for fact in transition.post_facts
    }
    return frozenset(
        fact
        for transition in materialized
        for fact in transition.pre_facts
        if fact not in produced and is_pure_init_relation_authority(fact)
    )
