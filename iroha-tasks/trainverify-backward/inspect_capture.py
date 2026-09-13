"""Read existing capture without rank-cell cache writes or recapture."""
import json
import pickle
from pathlib import Path
from nnscaler_backend.build_graph import _prepare_rank_cells
from verdict.graph import World, WType

ROOT = Path('/home/v-zhouziyu/trainverify-audits/general-parallel-internal1')
for name, label in [('global-b2', 's'), ('p2-r4', 'p')]:
    path = ROOT / name / 'capture.pkl'
    with path.open('rb') as stream:
        mg = pickle.load(stream)
    world = World(wtype=WType(label), plan_ndevs=len(mg.devices), runtime_ndevs=mg.runtime_ndevs,
                  **json.loads(path.with_suffix('.json').read_text()))
    cells = _prepare_rank_cells(world, mg, 0)
    backs = [c for c in cells if c.opname.name == 'BW_linear']
    print(name, 'cells', len(cells), 'BW_linear', len(backs))
    c = backs[0]
    fw = c.ir.mirror
    paired = [x for x in cells if x.ir is fw]
    print('node', c.node, 'paired', [(x.node, x.inputs, x.outputs) for x in paired])
    print('ins/outs', c.inputs, c.outputs, 'kwargs', c.kwargs)
    for title, irs in [('back-ir-inputs', c.ir.inputs()), ('back-ir-outputs', c.ir.outputs()),
                       ('saved', fw.inputs()), ('fw-outputs', fw.outputs()),
                       ('export-inputs', c._input_irs), ('export-outputs', c._output_irs)]:
        print(title)
        for t in irs:
            print(str(t), 'parent', getattr(getattr(t, 'parent', None), 'tid', None),
                  'grad', str(getattr(t, 'grad', None)))
