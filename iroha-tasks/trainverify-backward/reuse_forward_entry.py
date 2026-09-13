"""Reuse the accepted immutable forward entry for parameter-frame projections.

No entry/prefix recompilation and no shared-cache write. Only source/object
verified imports are linked into this lane's private overlay.
"""
import hashlib
import json
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
OLD = Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1/dp-prefix-cost-closure')
OUT = ROOT / '.hermes/backward-kernel/objects'

def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def link(source, expected, relative):
    source = Path(source)
    assert digest(source) == expected, source
    target = OUT / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    if not target.exists():
        target.symlink_to(source)
    assert digest(target) == expected, target


def source_pins(pins):
    for path, expected in pins.items():
        relative = path.split('/trainverify/', 1)[1]
        assert digest(ROOT / 'trainverify' / relative) == expected, path


def main():
    entry_root = OLD / 'output-projection'
    entry = json.loads((entry_root / 'actual-output-projection1-entry-kernel.json').read_text())
    assert entry['inner_exit'] == 0
    source = entry_root / 'actual-output-projection1/RuntimeWorld.lean'
    assert digest(source) == entry['source_sha256']
    pin = json.loads((OLD / 'initial-relations/SourceValueRead-kernel.json').read_text())
    source_pins(pin['sources'])
    for path, expected in pin['dependencies'].items():
        link(path, expected, Path(path).relative_to(OLD / 'initial-relations/objects'))
    for path, expected in entry['dependencies'].items():
        path = Path(path)
        if path.parent.name != 'denote':
            continue
        receipt_path = OLD / 'initial-relations' / (path.stem + '-kernel.json')
        if receipt_path.exists():
            receipt = json.loads(receipt_path.read_text())
            assert receipt['inner_exit'] == 0
            assert digest(ROOT / 'trainverify/denote' / (path.stem + '.lean')) == receipt['source_sha256']
            assert expected == receipt['object_sha256']
            source_pins(receipt['sources'])
            for dep, value in receipt['dependencies'].items():
                link(dep, value, Path(dep).relative_to(OLD / 'initial-relations/objects'))
        else:
            assert str(path) in pin['dependencies'] and expected == pin['dependencies'][str(path)]
        link(path, expected, Path('denote') / path.name)
    inventory = json.loads((entry_root / 'actual-output-projection1/world-receipt.json').read_text())['proof_bundle']['modules']
    checks = json.loads((OLD / 'post-transpose/actual-post-transpose1-kernel.json').read_text())
    for module in inventory:
        name = module['module']
        if not name.startswith('TrainVerifyRuntimePrefix'):
            continue
        check = next(row for row in checks if row['key'] == name)
        assert check['inner_exit'] == 0 and check['source_sha256'] == module['source_sha256']
        assert digest(entry_root / 'actual-output-projection1' / module['file']) == module['source_sha256']
        for dep, value in check['dependency_objects'].items():
            assert digest(dep) == value, dep
        link(entry_root / 'final-objects' / (name + '.olean'), check['object_sha256'], name + '.olean')
    for path, expected in entry['dependencies'].items():
        path = Path(path)
        if path.parent.name != 'denote':
            link(path, expected, path.name)
    link(entry_root / 'final-objects/RuntimeWorld.olean', entry['object_sha256'], 'RuntimeWorld.olean')
    print('accepted forward entry and dependency closure reused; no Lean run')

if __name__ == '__main__':
    main()
