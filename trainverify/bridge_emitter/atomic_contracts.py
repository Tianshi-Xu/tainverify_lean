"""Shared metadata gates for atomic backends with no extra authority premises."""


def validate_atomic_transition_contracts(relation, segment_id):
    chain = relation.dependent_chain_plan
    if chain is None or not chain.complete:
        raise ValueError("atomic backend requires a complete closed chain")
    segments = [s for s in chain.segments if s.segment_id == segment_id]
    if len(segments) != 1:
        raise ValueError("atomic segment identity is missing or ambiguous")
    segment = segments[0]
    owned = set(segment.transition_ids)
    transitions = [t for t in relation.transition_specs if t.transition_id in owned]
    if any(t.fact_only or t.authority_requirements for t in transitions):
        raise ValueError("atomic backend does not discharge extra transition authority or fact-only contracts")
    # Diagnostic segment fixtures may have no public anchor. When supplied, it
    # is protected on both boundaries, not merely against writes in the frame.
    anchor = chain.anchor_fact
    if anchor is not None:
        for state_id in (segment.pre_state_id, segment.post_state_id):
            states = [s for s in chain.states if s.state_id == state_id]
            if len(states) != 1 or anchor.fact_id not in states[0].fact_ids:
                raise ValueError("atomic frame must retain the public anchor on both boundaries")
