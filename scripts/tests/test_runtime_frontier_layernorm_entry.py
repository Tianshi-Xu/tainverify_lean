"""Static canonical wiring; actual-source and kernel gates remain separate."""
import ast
from pathlib import Path
from Verdict import runtime_initial_relations as initial


def test_frontier_layernorm_same_six_text_and_detail_before_codecs():
    attach = next(n for n in ast.parse(Path(initial.__file__).read_text()).body
                  if isinstance(n, ast.FunctionDef) and n.name == 'attach')
    imports = [n for n in ast.walk(attach) if isinstance(n, ast.ImportFrom)
               and n.module == 'Verdict.runtime_frontier_layernorm_values']
    assert len(imports) == 1, 'canonical frontier LayerNorm attachment missing'
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
               and any(isinstance(t, ast.Subscript) and ast.unparse(t) == "result['frontier_layernorm_values']"
                       for t in n.targets) for n in ast.walk(attach))
    predecessor = next(n for n in ast.walk(attach) if isinstance(n, ast.ImportFrom)
                       and n.module == 'Verdict.runtime_frontier_alias_exchange_values')
    assert predecessor.lineno < call.lineno
    for name in ('compact_binders', 'compact_reads'):
        codec = next(n for n in ast.walk(attach) if isinstance(n, ast.Call)
                     and isinstance(n.func, ast.Name) and n.func.id == name)
        assert call.lineno < codec.lineno
