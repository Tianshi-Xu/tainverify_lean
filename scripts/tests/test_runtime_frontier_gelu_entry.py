"""Static canonical wiring; actual-source and kernel gates remain separate."""
import ast
import pytest
from pathlib import Path
from Verdict import runtime_initial_relations as initial


def test_frontier_gelu_same_six_text_and_detail_before_codecs():
    attach = next(n for n in ast.parse(Path(initial.__file__).read_text()).body
                  if isinstance(n, ast.FunctionDef) and n.name == 'attach')
    imports = [n for n in ast.walk(attach) if isinstance(n, ast.ImportFrom)
               and n.module == 'Verdict.runtime_frontier_gelu_values']
    assert len(imports) == 1, 'canonical frontier GELU attachment missing'
    binding, = imports[0].names
    assert binding.name == 'render'
    call, = [n for n in ast.walk(attach) if isinstance(n, ast.Call)
             and isinstance(n.func, ast.Name) and n.func.id == binding.asname]
    expected = ast.parse("render(sm, pm, lineages, validation, bound, world.receipt['execution_order'])",
                         mode='eval').body
    assert isinstance(expected, ast.Call)
    assert [ast.dump(a) for a in call.args] == [ast.dump(a) for a in expected.args]
    assert not call.keywords
    assignment, = [n for n in ast.walk(attach) if isinstance(n, ast.Assign) and n.value is call]
    assert isinstance(assignment.targets[0], ast.Tuple)
    text, detail = assignment.targets[0].elts
    assert isinstance(text, ast.Name) and isinstance(detail, ast.Name)
    assert any(isinstance(n, ast.AugAssign) and ast.unparse(n.target) == 'entry'
               and any(isinstance(a, ast.Name) and a.id == text.id for a in ast.walk(n.value))
               for n in ast.walk(attach))
    assert any(isinstance(n, ast.Assign) and ast.unparse(n.value) == detail.id
               and any(isinstance(t, ast.Subscript) and ast.unparse(t) == "result['frontier_gelu_values']"
                       for t in n.targets) for n in ast.walk(attach))
    predecessor = next(n for n in ast.walk(attach) if isinstance(n, ast.ImportFrom)
                       and n.module == 'Verdict.runtime_frontier_linear_values')
    assert predecessor.lineno < call.lineno
    for name in ('compact_binders', 'compact_reads'):
        codec = next(n for n in ast.walk(attach) if isinstance(n, ast.Call)
                     and isinstance(n.func, ast.Name) and n.func.id == name)
        assert call.lineno < codec.lineno


def test_gelu_units_attach_exact_helper_pair():
    tree = ast.parse(Path(initial.__file__).read_text())
    render, = [n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'attach']
    condition = ast.dump(ast.parse("frontier_gelu_detail['units']", mode='eval').body)
    blocks = [n for n in ast.walk(render) if isinstance(n, ast.If) and ast.dump(n.test) == condition]
    assert len(blocks) == 1, 'GELU units must attach both helper imports'
    calls = [n for n in ast.walk(blocks[0]) if isinstance(n, ast.Call)
             and isinstance(n.func, ast.Attribute) and n.func.attr == 'replace']
    assert any(len(n.args) == 3 and isinstance(n.args[1], ast.Constant)
               and n.args[1].value == 'import denote.SourceSequenceHiddenExchange\nimport denote.SourceGeluRead\nimport denote.SourceGeluUnit\n'
               for n in calls)


def gelu_helpers():
    from scripts.tests.test_runtime_output_projection_exchange_entry import HELPERS
    hs = list(HELPERS)
    index = hs.index('SourceSequenceHiddenExchange') + 1
    hs[index:index] = ['SourceGeluRead', 'SourceGeluUnit']
    return hs


def test_gelu_helpers_are_admitted_in_order():
    from scripts.tests.test_runtime_output_projection_exchange_entry import source
    from Verdict.runtime_world import _proof_bundle
    text, support = source(gelu_helpers())
    imports = _proof_bundle(text, support)['modules'][-1]['imports']
    i = imports.index('denote.SourceGeluRead')
    assert imports[i:i+2] == ['denote.SourceGeluRead','denote.SourceGeluUnit']


@pytest.mark.parametrize('fault', ['read-only','unit-only','reorder','duplicate','missing-predecessor'])
def test_gelu_helper_pair_is_closed_and_not_repaired(fault):
    from scripts.tests.test_runtime_output_projection_exchange_entry import source
    from Verdict.runtime_world import _proof_bundle
    hs = gelu_helpers(); i = hs.index('SourceGeluRead')
    if fault == 'read-only': hs.remove('SourceGeluUnit')
    elif fault == 'unit-only': hs.remove('SourceGeluRead')
    elif fault == 'reorder': hs[i:i+2] = hs[i:i+2][::-1]
    elif fault == 'duplicate': hs.insert(i, 'SourceGeluRead')
    else: hs.remove('SourceSequenceHiddenExchange')
    text,support = source(hs)
    with pytest.raises(ValueError, match='import membership mismatch'):
        _proof_bundle(text,support)
