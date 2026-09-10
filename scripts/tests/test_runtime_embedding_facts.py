"""Static shared embedding facts; Lean compilation belongs to the parent."""
from pathlib import Path

import pytest

from Verdict import runtime_embedding_units as direct
from Verdict import runtime_embedding_position_units as position
from scripts.tests.test_runtime_embedding_position_units import prepared


@pytest.mark.parametrize('D,T,seqlen', [(2, 2, 2), (3, 2, 2), (2, 3, 6)])
@pytest.mark.parametrize('kind', ['direct', 'position'])
@pytest.mark.parametrize('reverse_specs', [False, True])
def test_shared_facts_preserve_value_headers_and_source_contract(D, T, seqlen, kind, reverse_specs):
    args = prepared(D, T, seqlen)
    if reverse_specs:
        args[4]['relations'].reverse()
        for relation in args[4]['relations']:
            relation['units'].reverse()
    if kind == 'direct':
        text, detail = direct.render(*args[:3], args[4])
        prefix, helper = 'embeddingUnit', 'fw_embedding_dp_tp_unit_facts_of_source_eqs'
    else:
        text, detail = position.render(*args)
        prefix, helper = 'embeddingPositionUnit', 'fw_embedding_dp_tp_position_unit_facts_of_source_eqs'
    assert len(detail['units']) == D
    assert text.count('initialParameterValues_final s p t q hs hp h') == D
    assert text.count(helper) == D
    assert detail['lean_bytes'] == len(text.encode())
    old_positions = []
    for row in detail['units']:
        u, out = row['unit'], row['sm_output_tid']
        name, facts = f'{prefix}_{out}_{u}', f'{prefix}Facts_{out}_{u}'
        assert row['theorem'] == name
        assert row['facts_theorem'] == facts
        outputs = '[' + ', '.join(f'q {tid}' for tid in row['pm_output_tids']) + ']'
        contract = (' (s p t q : Store)\n'
            '    (hs : smDenoteWithInputs s = some t) (hp : pmDenoteWithInputs p = some q)\n'
            '    (h : InitialParameterValues s p) :\n')
        value = (f'    chunkPrimDimN 0 {D} {u} (t {out}) =\n'
            f'    allGatherPrimDimN 2 {T} 0 {outputs} := by')
        header = f'theorem {name}' + contract + value
        assert header + f'\n  exact ({facts} s p t q hs hp h).2.2' in text
        old_positions.append(text.index(header))
        facts_body = text.split(f'theorem {facts}' + contract, 1)[1].split(f'theorem {name}', 1)[0]
        if kind == 'position':
            dims = row['dimensions']; B, S, H = (dims[k] for k in ('B', 'S', 'H'))
            localshape = [B, S * T, H]
        else:
            activation = next(l for l in args[2] if l.target.tid == out)
            localshape = list(activation.units[u].pieces[0].endpoint.shape)
        fullshape = [localshape[0] * D, localshape[1], localshape[2] * T]
        assert facts_body.startswith(f'    (t {out}).shape = {fullshape} ∧\n'
            f'    (∀ x ∈ {outputs}, x.shape = {localshape}) ∧\n' + value)
        spec = row['spec_index']
        count = sum(len(r['units']) for r in args[4]['relations'])
        projection = 'hrels' + '.2' * spec + ('.1' if spec < count - 1 else '')
        assert f':= {projection}\n' in facts_body
        assert facts_body.count(helper) == 1
    assert old_positions == sorted(old_positions)
    for forbidden in ('native_decide', 'sorry', 'admit', 'fw_allToAllPrim', 'hactivation'):
        assert forbidden not in text


def test_generic_facts_have_identical_source_premises():
    root = Path(__file__).resolve().parents[2] / 'trainverify' / 'denote'
    facts = root / 'SourceEmbeddingFacts.lean'
    assert facts.exists(), 'generic source embedding facts missing'
    text = facts.read_text()
    for module, old, new in [
        ('SourceEmbeddingUnit', 'fw_embedding_dp_tp_unit_of_source_eqs',
         'fw_embedding_dp_tp_unit_facts_of_source_eqs'),
        ('SourceEmbeddingPositionUnit', 'fw_embedding_dp_tp_position_unit_of_source_eqs',
         'fw_embedding_dp_tp_position_unit_facts_of_source_eqs'),
    ]:
        original = (root / f'{module}.lean').read_text()
        original_args = original.split(f'theorem {old}', 1)[1].split(' :\n', 1)[0]
        new_args = text.split(f'theorem {new}', 1)[1].split(' :\n', 1)[0]
        assert new_args == original_args
        assert f'exact {old} ' in text
    assert 'globalOut.shape = [B * D, S, H * T] ∧' in text
    assert '(∀ x ∈ unitOuts, x.shape = [B, S, H]) ∧' in text
    assert 'globalOut.shape = [B * D, S * T, H * T] ∧' in text
    assert '(∀ x ∈ AAoutputs, x.shape = [B, S * T, H]) ∧' in text
    assert 'AllToAllSourceFaithful.tensor_shape' in text
    for forbidden in ('native_decide', 'sorry', 'admit', 'fw_allToAllPrim'):
        assert forbidden not in text
