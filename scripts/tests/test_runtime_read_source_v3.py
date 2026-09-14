"""Opt-in fixed-vocabulary v3, with legacy bytes kept independent."""
import pytest
from Verdict import runtime_read_source as codec


def sample(helper='SourceMatmulRead.matmul_value_of_split'):
    prefix = f'{helper} pmGraph pmScope pmPeers pmGraph.nodes\n    pmInputRequests'
    return ('namespace TrainVerify.Denote.RuntimeWorld\n' + ''.join(
        f'theorem probe{i} : True := by\n  apply {prefix} xs\n#print axioms probe{i}\n'
        for i in range(12)) + 'end TrainVerify.Denote.RuntimeWorld\n')


def test_v3_explicit_prefix_exact_inverse():
    text = sample()
    packed = codec.compact(text, version=3)
    assert '-- RuntimeReadSource v3\n' in packed
    assert 'local notation "vP0" => SourceMatmulRead.matmul_value_of_split' in packed
    assert codec.expand(packed) == text
    assert len(packed.encode()) < len(codec.compact(text).encode())


@pytest.mark.parametrize('status', [None, 'unvalidated', 'current-run-parameter-values-validated'])
def test_attachment_selects_v3_only_from_validated_seed_mode(status):
    import ast
    from pathlib import Path
    from types import SimpleNamespace
    from Verdict import runtime_initial_relations as initial
    tree = ast.parse(Path(initial.__file__).read_text())
    attach = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == 'attach')
    start = next(i for i, n in enumerate(attach.body) if isinstance(n, ast.ImportFrom)
                 and n.module == 'Verdict.runtime_binder_source')
    stop = next(i for i, n in enumerate(attach.body) if isinstance(n, ast.Assign)
                and any(isinstance(v, ast.Call) and isinstance(v.func, ast.Name)
                        and v.func.id == '_proof_bundle' for v in ast.walk(n)))
    receipt = {} if status is None else {'seed_input': {'parameter_inputs': {'status': status}}}
    text = sample()
    env = {'entry': text, 'world': SimpleNamespace(receipt=receipt)}
    exec(compile(ast.Module(body=attach.body[start:stop], type_ignores=[]), initial.__file__, 'exec'), env)
    expected = codec.compact(text, version=3 if status == 'current-run-parameter-values-validated' else 2)
    assert env['entry'] == expected


@pytest.mark.parametrize('term', ['List.Forall₂.nil', 'List.ofFn', 'transposeAxes'])
def test_v3_explicit_application_is_fail_closed(term):
    # @ applies to the notation node, not its expanded RHS in Lean.
    text = ''.join(f'def p{i} := @{term}\n' for i in range(20)) + sample()
    assert codec.compact(text, version=3) == text


@pytest.mark.parametrize('term', ['List.Forall₂.nil', 'List.mem_cons'])
def test_v3_named_application_is_fail_closed(term):
    text = ''.join(f'def p{i} := {term} (R := relation)\n' for i in range(20)) + sample()
    assert codec.compact(text, version=3) == text
