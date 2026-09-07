"""In-memory conditional witnesses for the interleaved shared embedding prefix."""
from types import SimpleNamespace as NS


def renderer_fixture(k=2):
    from trainverify.bridge_emitter import relation_compiler as rc
    from trainverify.bridge_emitter.parser import Node
    if type(k) is not int or k < 1:
        raise ValueError("positive K required")
    hs = rc.RelationFactSpec('sharded', ('init:50', *(f'init:{60+r}' for r in range(k))), gather_dim=1)
    ho = rc.RelationFactSpec('sharded', ('sm:0:0', *(f'pm:{2*r}:0' for r in range(k))), gather_dim=2)
    ids = rc.RelationFactSpec('chunked', ('init:41', *(f'pm:{2*r+1}:0' for r in range(k))), gather_dim=1)
    out = rc.RelationFactSpec('sharded', ('sm:1:0', *(f'pm:{2*k+r}:0' for r in range(k))), gather_dim=1)
    records = (
        rc.ClosedRelationFactRecord('weight', hs, 'sharded', 50, tuple(60+r for r in range(k)), None, None, (7, 4*k), (7, 4), gather_dim=1),
        rc.ClosedRelationFactRecord('hidden_out', ho, 'sharded', 100, tuple(200+r for r in range(k)), None, None, (1, 2*k, 4*k), (1, 2*k, 4), gather_dim=2),
        rc.ClosedRelationFactRecord('ids_out', ids, 'chunked', 41, tuple(300+r for r in range(k)), None, None, (1, 2*k), (1, 2), gather_dim=1),
        rc.ClosedRelationFactRecord('sequence_out', out, 'sharded', 101, tuple(400+r for r in range(k)), None, None, (1, 2*k, 12), (1, 2, 12), gather_dim=1),
    )
    hc = rc.KRankHiddenShardedEmbeddingCertificate('embedding-hidden-sharded-k-rank', k, 40, (1, 2*k), (7, 4*k), (7, 4), (1, 2*k, 4*k), (1, 2*k, 4), hs, ho, 'sm:0:0', tuple(f'pm:{2*r}:0' for r in range(k)), 'TrainVerify.Denote.fw_embedding_hidden_shards_k_rank')
    sc = rc.KRankShardedIdsEmbeddingCertificate('embedding-sharded-ids-k-rank', k, 1, 41, 51, (1, 2*k), (1, 2), (7, 12), (1, 2*k, 12), (1, 2, 12), ids, out, 'sm:1:0', tuple(f'pm:{2*r+1}:0' for r in range(k)), tuple(f'pm:{2*k+r}:0' for r in range(k)), 'TrainVerify.Denote.fw_embedding_allGatherPrimDimN_dim1_shared_weight')
    transitions = (
        rc.CertificateTransitionSpec('hidden', hc.rule_id, (hs,), (ho,), (0,), tuple(2*r for r in range(k)), hc.lean_theorem),
        rc.CertificateTransitionSpec('sequence', sc.rule_id, (), (ids, out), (1,), tuple(2*r+1 for r in range(k))+tuple(2*k+r for r in range(k)), sc.lean_theorem),
    )
    from dataclasses import replace
    from trainverify.bridge_emitter.composer import _typed_certificate_digest
    transitions = tuple(replace(t, certificate_digest=_typed_certificate_digest(c)) for t, c in zip(transitions, (hc, sc)))
    auth = tuple(x for tid, shape in ((40, (1, 2*k)), (41, (1, 2*k)), (51, (7, 12))) for x in (
        rc.ClosedTensorEqFactRecord(f'eq_{tid}', 'sm', tid, 'pm', tid),
        rc.ClosedTensorShapeFactRecord(f'shape_{tid}', 'pm', tid, shape, tid)))
    anchor = rc.ClosedTensorShapeFactRecord('anchor', 'sm', 999, (1,), 999)
    before = rc.ClosedRelationStateRecord('state_before', ('anchor', 'weight', *(a.fact_id for a in auth)))
    after = rc.ClosedRelationStateRecord('state_after', (*before.fact_ids, 'hidden_out', 'ids_out', 'sequence_out'))
    sm = [Node(0, 'FW_embedding', [40, 50], [100], []), Node(0, 'FW_embedding', [41, 51], [101], [])]
    pm = []
    for r in range(k):
        pm.extend([Node(r, 'FW_embedding', [40, 60+r], [200+r], []), Node(r, 'ChunkPrim', [41], [300+r], [1])])
    pm.extend(Node(r, 'FW_embedding', [300+r, 51], [400+r], []) for r in range(k))
    segment = rc.ClosedDependentSegmentRecord('segment_000000', 'component', before.state_id, after.state_id, ('hidden', 'sequence'), (0, len(sm)), (0, len(pm)))
    chain = NS(complete=True, relation_facts=records, authority_facts=auth, anchor_fact=anchor, states=(before, after), segments=(segment,))
    return NS(sm_nodes=sm, pm_nodes=pm, sm_num_ranks=1, pm_num_ranks=k, sm_graph_ref='Fixture.sm', pm_graph_ref='Fixture.pm'), NS(dependent_chain_plan=chain, certificates=(hc, sc), transition_specs=transitions), segment.segment_id


def real_prefix_fixture(export, goal_ids=tuple(range(1, 27))):
    """Read an actual exported shared DAG using this checkout's class identities.

    Returns (ir, global_relation, first_segment_id); never writes artifacts.
    Parser configuration is restored even when loading fails.
    """
    from pathlib import Path
    from dataclasses import replace
    from trainverify.bridge_emitter import parser
    from trainverify.bridge_emitter.model_authority import load_model_authority, materialize_target_ir
    from trainverify.bridge_emitter.model_compiler import compile_shared_proof_dag, compile_shared_relation_dag
    from trainverify.bridge_emitter.proof_compiler import build_default_registry
    export = Path(export).resolve()
    names = ('DENOTE_DIR', 'GEN_DIR', 'GEN_FILE', 'MOD_PREFIX')
    old = tuple(getattr(parser, key) for key in names)
    try:
        parser.DENOTE_DIR = parser.GEN_DIR = str(export)
        parser.GEN_FILE, parser.MOD_PREFIX = 'GeneratedData.lean', 'FreshGPT'
        model = load_model_authority(goal_ids, str(export.parent), model_id='conditional-prefix', allow_partial=False)
        dag = compile_shared_relation_dag(model, compile_shared_proof_dag(model, build_default_registry()))
        representative = max(dag.projections.values(), key=lambda p: (len(p.transition_keys), -p.goal_id))
        lineages = {}
        init_ids = set()
        for query in model.targets.values():
            init_ids.update(query.full_init_goal_ids)
            for tid, lineage in query.init_lineages.items():
                if tid in lineages and lineages[tid] != lineage:
                    raise ValueError('conflicting shared InitGoal authority')
                lineages[tid] = lineage
        ir = replace(materialize_target_ir(model, representative.goal_id), init_lineages=lineages, full_init_goal_ids=tuple(sorted(init_ids)))
        relation = dag.global_relation
        if relation is None or relation.dependent_chain_plan is None:
            raise ValueError('shared global relation/chain is missing')
        return ir, relation, relation.dependent_chain_plan.segments[0].segment_id
    finally:
        for key, value in zip(names, old):
            setattr(parser, key, value)


def conditional_prefix_witness(ir, relation, segment_id, namespace='ConditionalEmbeddingPrefix', graph_imports=()):
    """Exact selected pre/post-state witness, with caller-supplied graph imports.

    Keeps the real frame and all its public/anchor authority; excludes unrelated
    later states and facts only. Returns bytes-as-source, without filesystem I/O.
    """
    from trainverify.bridge_emitter.composer import render_closed_relation_declarations
    from trainverify.bridge_emitter.embedding_hidden_ids_renderer import render_closed_embedding_hidden_ids_segment
    chain = relation.dependent_chain_plan
    segments = [s for s in chain.segments if s.segment_id == segment_id]
    if len(segments) != 1:
        raise ValueError('one exact segment required')
    segment = segments[0]
    states = tuple(s for s in chain.states if s.state_id in (segment.pre_state_id, segment.post_state_id))
    live = {fid for state in states for fid in state.fact_ids}
    # Semantic intermediates may be retired at the post-state, but their named
    # facts are still used by the same unchanged renderer proof.
    transitions = [t for t in relation.transition_specs if t.transition_id in segment.transition_ids]
    needed = {f for t in transitions for f in (*t.pre_facts, *t.post_facts)}
    selected = NS(complete=True, anchor_fact=chain.anchor_fact, states=states,
        relation_facts=tuple(f for f in chain.relation_facts if f.fact_id in live or f.source in needed),
        authority_facts=tuple(f for f in chain.authority_facts if f.fact_id in live), segments=(segment,))
    declarations = render_closed_relation_declarations(selected, namespace)
    suffix = f'end\nend TrainVerify.Denote.{namespace}\n'
    if not declarations.endswith(suffix):
        raise ValueError('declaration namespace boundary changed')
    imports = [line for line in declarations.splitlines() if line.startswith('import ')]
    body = '\n'.join(line for line in declarations[:-len(suffix)].splitlines() if not line.startswith('import '))
    return '\n'.join([*imports, 'import denote.EmbeddingHiddenShard', 'import denote.EmbeddingSequenceShard',
        *(f'import {name}' for name in graph_imports), 'set_option maxHeartbeats 500000', body,
        render_closed_embedding_hidden_ids_segment(ir, relation, segment_id), f'#print axioms {segment_id}', suffix])


def witness_source(k=2):
    from trainverify.bridge_emitter.composer import _node_text, render_closed_relation_declarations
    from trainverify.bridge_emitter.embedding_hidden_ids_renderer import render_closed_embedding_hidden_ids_segment
    ir, relation, sid = renderer_fixture(k)
    namespace = f'EmbeddingHiddenIdsK{k}'
    ir.sm_graph_ref, ir.pm_graph_ref = f'{namespace}Graph.sm', f'{namespace}Graph.pm'
    declarations = render_closed_relation_declarations(relation.dependent_chain_plan, namespace)
    suffix = f'end\nend TrainVerify.Denote.{namespace}\n'
    assert declarations.endswith(suffix)
    imports = [line for line in declarations.splitlines() if line.startswith('import ')]
    body = '\n'.join(line for line in declarations[:-len(suffix)].splitlines() if not line.startswith('import '))
    return '\n'.join([*imports, 'import denote.EmbeddingHiddenShard', 'import denote.EmbeddingSequenceShard', 'set_option maxHeartbeats 500000', 'open TrainVerify.Denote', f'namespace {namespace}Graph', 'def sm : GraphDecl := { numRanks := 1, nodes := [' + ', '.join(map(_node_text, ir.sm_nodes)) + '] }', f'def pm : GraphDecl := {{ numRanks := {k}, nodes := [' + ', '.join(map(_node_text, ir.pm_nodes)) + '] }', f'end {namespace}Graph', body, render_closed_embedding_hidden_ids_segment(ir, relation, sid), '#print axioms segment_000000', suffix])
