"""Lightweight capture-boundary tests; real CUDA runs are separate integration gates."""
from types import SimpleNamespace
import pytest
from scripts.gpt_capture import capture_codegen


@pytest.mark.parametrize('policy', ['pp', 'hybrid', 'autodist'])
def test_capture_rejects_policy_without_world_scope(tmp_path, policy):
    import json
    import subprocess
    import sys
    cfg = tmp_path / 'config.json'
    cfg.write_text(json.dumps({'policy': policy}))
    out = tmp_path / 'capture'
    result = subprocess.run([sys.executable, '-m', 'scripts.gpt_capture',
                             '--config', str(cfg), '--out', str(out)],
                            capture_output=True, text=True)
    assert result.returncode != 0
    assert 'only builtin tp/dp policies' in result.stderr
    assert not out.exists()


def test_real_capture_cli(tmp_path):
    import json
    import os
    import subprocess
    from pathlib import Path
    import pytest
    python = os.environ.get('TV_CAPTURE_PYTHON')
    if not python:
        pytest.skip('set TV_CAPTURE_PYTHON to the CUDA/nnScaler environment')
    config = {
        'model': {'hidden': 32, 'layers': 1, 'heads': 4, 'ffn_hidden_dim': 64,
                  'num_embeddings': 64, 'seqlen': 8},
        'compute': {'plan_ngpus': 2, 'runtime_ngpus': 4, 'use_zero': 0,
                    'use_end2end': True, 'constant_folding': True,
                    'trace_strategy': 'cuda_run_cpu_offload',
                    'pas_config': {'seed': 7}},
        'policy': 'tp', 'batch_size': 1, 'seed': 7,
    }
    cfg = tmp_path / 'config.json'
    cfg.write_text(json.dumps(config))
    out = tmp_path / 'capture'
    root = Path(__file__).resolve().parents[2]
    result = subprocess.run([python, '-m', 'scripts.gpt_capture', '--config', str(cfg),
                             '--out', str(out)], cwd=root, capture_output=True, text=True)
    assert result.returncode == 0, result.stdout + result.stderr
    assert (out / 'capture.pkl').is_file(), result.stdout + result.stderr
    receipt = json.loads((out / 'capture.receipt.json').read_text())
    assert receipt['compute']['plan_ngpus'] == 2
    assert receipt['compute']['runtime_ngpus'] == 4
    assert receipt['devices'] == [0, 1]
    assert receipt['runtime_ngpus'] == 4
    assert receipt['cuda_forward_backward'] is True
    assert len(list((out / 'code').rglob('gencode*.py'))) == 4


def test_capture_observes_real_constructor_and_restores_it():
    made = []
    def real(*args, **kwargs):
        result = SimpleNamespace(args=args, kwargs=kwargs)
        made.append(result)
        return result
    module = SimpleNamespace(ModuleCodeGen=real)
    with capture_codegen(module) as captures:
        actual = module.ModuleCodeGen('plan', runtime_ngpus=4)
        assert actual is made[0]
        assert captures == [actual]
        assert actual.args == ('plan',)
        assert actual.kwargs == {'runtime_ngpus': 4}
    assert module.ModuleCodeGen is real


def test_capture_restores_constructor_after_compile_failure():
    import pytest
    real = object
    module = SimpleNamespace(ModuleCodeGen=real)
    with pytest.raises(RuntimeError, match='compile failed'):
        with capture_codegen(module):
            raise RuntimeError('compile failed')
    assert module.ModuleCodeGen is real
