"""Canonical wiring is static evidence; real source/kernel gates stay separate."""
import ast
from pathlib import Path
from Verdict import runtime_initial_relations as initial


def test_canonical_frontier_alias_exchange_uses_same_six_before_codecs():
    attach = next(n for n in ast.parse(Path(initial.__file__).read_text()).body
                  if isinstance(n, ast.FunctionDef) and n.name == 'attach')
    imports = [n for n in ast.walk(attach) if isinstance(n, ast.ImportFrom)
               and n.module == 'Verdict.runtime_frontier_alias_exchange_values']
    assert len(imports) == 1, 'canonical frontier alias/exchange attachment missing'
    binding, = imports[0].names
    assert binding.name == 'render'
    calls = [n for n in ast.walk(attach) if isinstance(n, ast.Call)
             and isinstance(n.func, ast.Name) and n.func.id == binding.asname]
    call, = calls
    expected = ast.parse("render(sm, pm, lineages, validation, bound, world.receipt['execution_order'])",
                         mode='eval').body
    assert [ast.dump(a) for a in call.args] == [ast.dump(a) for a in expected.args]
    assert not call.keywords
    residual = next(n for n in ast.walk(attach) if isinstance(n, ast.ImportFrom)
                    and n.module == 'Verdict.runtime_attention_residual_values')
    assert residual.lineno < call.lineno
    for name in ('compact_binders', 'compact_reads'):
        codec = next(n for n in ast.walk(attach) if isinstance(n, ast.Call)
                     and isinstance(n.func, ast.Name) and n.func.id == name)
        assert call.lineno < codec.lineno
    assignments = [n for n in ast.walk(attach) if isinstance(n, ast.Assign)
                   and any(isinstance(t, ast.Subscript)
                           and ast.unparse(t) == "result['frontier_alias_exchange_values']"
                           for t in n.targets)]
    assert len(assignments) == 1
