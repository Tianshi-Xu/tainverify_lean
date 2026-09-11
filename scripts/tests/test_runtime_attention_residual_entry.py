"""Static SAME-six canonical call contract; actual source/kernel gates are separate."""
import ast
from pathlib import Path
from Verdict import runtime_initial_relations as initial


def test_canonical_residual_calls_same_six_before_compaction():
    tree = ast.parse(Path(initial.__file__).read_text())
    attach = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'attach')
    imports = [n for n in ast.walk(attach) if isinstance(n, ast.ImportFrom)
               and n.module == 'Verdict.runtime_attention_residual_values']
    assert len(imports) == 1, 'canonical residual source attachment missing'
    binding, = imports[0].names
    assert binding.name == 'render'
    calls = [n for n in ast.walk(attach) if isinstance(n, ast.Call)
             and isinstance(n.func, ast.Name) and n.func.id == binding.asname]
    call, = calls
    expected = ast.parse("render(sm, pm, lineages, validation, bound, world.receipt['execution_order'])", mode='eval').body
    assert [ast.dump(a) for a in call.args] == [ast.dump(a) for a in expected.args]
    assert not call.keywords
    compact = next(n for n in ast.walk(attach) if isinstance(n, ast.Call)
                   and isinstance(n.func, ast.Name) and n.func.id == 'compact_binders')
    assert call.lineno < compact.lineno
    assignments = [n for n in ast.walk(attach) if isinstance(n, ast.Assign)
                   and any(isinstance(t, ast.Subscript) and ast.unparse(t) == "result['attention_residual_values']" for t in n.targets)]
    assert len(assignments) == 1
