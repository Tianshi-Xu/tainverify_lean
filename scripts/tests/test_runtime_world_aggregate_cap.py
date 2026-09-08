"""Runtime-world's complete UTF-8 source budget, independent of per-file scans."""
import hashlib
import json
from unittest.mock import patch

import pytest

from Verdict import graph_to_lean as c, runtime_prefix as p, runtime_world as w

LIMIT = 2_500_000


def bundle(total=None, unicode=False):
    """Valid import chain and authentic support; pad only Lean comments, not proofs."""
    chunk = p.PREFIX_MODULE + '0000.lean'
    imports = f'import {w.WORLD_DATA_MODULE}\nimport denote.SourceScopedPrefix\nimport {p.SUPPORT_MODULE}\n'
    sources = {w.WORLD_DATA_FILE: 'import denote.SourceScopedEval\n',
               p.SUPPORT_FILE: p.support_source(), chunk: imports}
    entry = imports + f'import {p.PREFIX_MODULE}0000\n'
    texts = [sources[w.WORLD_DATA_FILE], sources[chunk], entry]
    if total is not None:
        remaining = total - sum(len(t.encode('utf-8')) for t in [*sources.values(), entry])
        assert remaining >= 9
        for i in range(3):
            size = remaining // (3 - i)
            remaining -= size
            body = size - 3
            padding = ('é' * (body // 2) + ' ' * (body % 2)) if unicode else ' ' * body
            texts[i] += '--' + padding + '\n'
        sources[w.WORLD_DATA_FILE], sources[chunk], entry = texts
    # Rebuild production inventory under a test-only permissive budget so publish
    # sees a fresh, otherwise-valid receipt, never a stale hash rejection.
    with patch.object(c, 'GENERATED_LEAN_SOURCE_LIMIT', 10_000_000):
        receipt = dict(proof_bundle=w._proof_bundle(entry, sources), source_only=True,
                       proof_admissible=False)
    return w.WorldDefinitions(entry, receipt, sources)


def test_healthy_bundle_publishes_exact_sources_and_inventory(tmp_path):
    artifact = bundle()
    out = tmp_path / 'healthy' / 'World.lean'
    w.publish(artifact, out)
    assert out.read_text() == artifact.lean
    receipt = json.loads((out.parent / 'world-receipt.json').read_text())
    assert receipt['proof_bundle'] == w._proof_bundle(artifact.lean, artifact.supporting_sources, out.name)
    for module in receipt['proof_bundle']['modules']:
        data = (out.parent / module['file']).read_bytes()
        assert hashlib.sha256(data).hexdigest() == module['source_sha256']
    assert receipt['proof_admissible'] is False


@pytest.mark.parametrize('delta', [-1, 0, 1])
@pytest.mark.parametrize('unicode', [False, True])
def test_real_threshold_complete_bundle(tmp_path, delta, unicode):
    artifact = bundle(LIMIT + delta, unicode)
    texts = [artifact.lean, *artifact.supporting_sources.values()]
    assert sum(len(t.encode('utf-8')) for t in texts) == LIMIT + delta
    assert all(len(t.encode('utf-8')) < LIMIT for t in texts)
    if unicode:
        assert sum(map(len, texts)) < LIMIT
    out = tmp_path / 'fresh' / 'World.lean'
    if delta < 0:
        w.publish(artifact, out)
        assert sum(f.stat().st_size for f in out.parent.glob('*.lean')) == LIMIT - 1
    else:
        with pytest.raises(ValueError, match='world bundle.*byte limit'):
            w._proof_bundle(artifact.lean, artifact.supporting_sources)
        with pytest.raises(ValueError, match='world bundle.*byte limit'):
            w.publish(artifact, out)
        assert list(tmp_path.iterdir()) == []


def test_all_roles_count_and_rejection_precedes_any_staging_or_destination_guard(tmp_path):
    artifact = bundle()
    total = sum(len(t.encode('utf-8')) for t in [artifact.lean, *artifact.supporting_sources.values()])
    # At this small test-only budget, omitting ANY data/support/chunk/entry passes
    # incorrectly. No production knob or source exclusion is introduced.
    out = tmp_path / 'existing' / 'World.lean'
    out.parent.mkdir()
    out.write_bytes(b'keep existing source\n')
    sentinel = out.parent / 'sentinel'
    sentinel.write_bytes(b'keep unrelated bytes\x00')
    before = {str(f.relative_to(tmp_path)): f.read_bytes() for f in tmp_path.rglob('*') if f.is_file()}
    with patch.object(c, 'GENERATED_LEAN_SOURCE_LIMIT', total):
        with patch.object(w.tempfile, 'TemporaryDirectory', side_effect=AssertionError('staging reached')):
            with patch.object(c, '_validate_definitions_only_destination', side_effect=AssertionError('destination guard reached')):
                with pytest.raises(ValueError, match='world bundle.*byte limit'):
                    w.publish(artifact, out)
    assert before == {str(f.relative_to(tmp_path)): f.read_bytes() for f in tmp_path.rglob('*') if f.is_file()}
    assert sorted(f.name for f in tmp_path.iterdir()) == ['existing']


def test_authentic_renderer_and_publish_share_aggregate_gate(tmp_path):
    from scripts.tests.test_runtime_scoped_prefix import collective_world
    root = tmp_path / 'input'
    root.mkdir()
    artifact = collective_world(root, 2, chain=True)
    out = tmp_path / 'healthy' / 'World.lean'
    w.publish(artifact, out)
    assert out.read_text() == artifact.lean
    total = sum(len(t.encode('utf-8')) for t in [artifact.lean, *artifact.supporting_sources.values()])
    second = tmp_path / 'second-input'
    second.mkdir()
    with patch.object(c, 'GENERATED_LEAN_SOURCE_LIMIT', total):
        with pytest.raises(ValueError, match='world bundle.*byte limit'):
            collective_world(second, 2, chain=True)
        with pytest.raises(ValueError, match='world bundle.*byte limit'):
            w.publish(artifact, tmp_path / 'blocked' / 'World.lean')
    assert not (tmp_path / 'blocked').exists()
    assert not list(tmp_path.glob('trainverify-world-*'))
