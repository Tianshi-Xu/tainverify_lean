"""Deterministic exact-source witnesses for both generic BW-embedding renderers."""
from types import SimpleNamespace
from scripts.tests.test_bw_embedding_sequence_k import renderer_fixture, vocab_renderer_fixture
from trainverify.bridge_emitter.composer import _node_text, render_closed_relation_declarations
from trainverify.bridge_emitter.bw_embedding_sequence_renderer import render_closed_k_rank_bw_embedding_sequence_segment
from trainverify.bridge_emitter.bw_embedding_vocab_renderer import render_closed_k_rank_bw_embedding_vocab_segment


def render(cases=((1, 3, 2, 5, 11), (2, 1, 8, 64, 16), (3, 2, 5, 7, 13), (4, 1, 4, 64, 16))):
    chunks = ['import denote.GraphGears', 'import denote.BWEmbeddingSequenceShardK',
              'import denote.BWEmbeddingVocabShardK', 'import denote.RelationCompiler',
              'open TrainVerify.Denote', '']
    families = (
        ('Seq', cases, renderer_fixture, render_closed_k_rank_bw_embedding_sequence_segment),
        ('Vocab', tuple((k, 5, 7) for k in (1, 2, 3, 4)), vocab_renderer_fixture,
         render_closed_k_rank_bw_embedding_vocab_segment),
    )
    for family, dimensions, make_fixture, renderer in families:
        for dims in dimensions:
            k = dims[0]
            ir, relation, segment = make_fixture(*dims)
            graph_ns, namespace = f'BW{family}GraphK{k}', f'GeneratedBW{family}K{k}'
            ir.sm_graph_ref, ir.pm_graph_ref = f'{graph_ns}.sm', f'{graph_ns}.pm'
            chunks.extend([
                f'namespace {graph_ns}',
                'def sm : GraphDecl := { numRanks := 1, nodes := [' + ', '.join(_node_text(n) for n in ir.sm_nodes) + '] }',
                f'def pm : GraphDecl := {{ numRanks := {k}, nodes := [' + ', '.join(_node_text(n) for n in ir.pm_nodes) + '] }',
                f'end {graph_ns}',
            ])
            chain = relation.dependent_chain_plan
            chain.complete = True  # Complete conditional fixture, not whole-model closure.
            chain.anchor_fact = SimpleNamespace(fact_id='unused_anchor', side='sm', tid=1,
                                               shape=chain.relation_facts[0].full_shape)
            declarations = render_closed_relation_declarations(chain, namespace)
            suffix = f'end\nend TrainVerify.Denote.{namespace}\n'
            assert declarations.endswith(suffix)
            body = '\n'.join(line for line in declarations[:-len(suffix)].splitlines()
                             if not line.startswith('import '))
            proof = renderer(ir, relation, segment)
            chunks.extend([body, proof, '#print axioms segment_000000_sound', suffix])
    return '\n'.join(chunks)
