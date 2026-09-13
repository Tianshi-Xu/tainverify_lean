"""Source-seeded PM cotangent values composed from the existing shared DAG.

This module emits only dependent value projections. The initial shape contract
and original successful run remain explicit. Fresh seed/collective/source
binding precedes theorem selection; no capture shape is a Lean premise.
"""
from Verdict import runtime_backward_cotangent_reads as cotangents
from Verdict import runtime_backward_prefix_shapes as shapes
from Verdict.runtime_lineage import _same_typed


def render(worlds, config, prefix, rank_code_directory):
    _, prior = cotangents.render(worlds, config, config['pm_run'], rank_code_directory)
    view, cells, _, _, label = worlds[1]
    if label != 'pm':
        raise ValueError('bw-constant original PM world required')
    indices = []
    for row in prior['reads']:
        matches = [i for i, cell in enumerate(cells)
                   if cell.opname.name == 'BW_linear'
                   and list(cell.inputs[0]) == row['output_ref']]
        if len(matches) != 1:
            raise ValueError('bw-constant unique original linear consumer required')
        indices.append(matches[0])
    _, projected = shapes.render(worlds, indices, prefix, seed_config=config)
    seed_shapes = {tuple(r['ref']): r for r in projected['reads'] if r['role'] == 'seed_primal'}
    proof, rows = [], []
    for row in prior['reads']:
        if not _same_typed(row['params'], [1, 2]):
            raise ValueError('bw-constant faithful reverse dimensions must be [1,2]')
        node = view.nodes()[row['source_index']]
        scope = view.collective_scopes[node]
        ordered = []
        for tensor in view.node_inputs(node):
            producers = [cell for cell in cells if tuple(view.source_tensor(tensor)) in cell.outputs]
            if len(producers) != 1 or producers[0].opname.name != 'BW_sum':
                raise ValueError('bw-constant original ordered BW_sum producer required')
            saved_ref = tuple(producers[0].inputs[1])
            if saved_ref not in seed_shapes:
                raise ValueError('bw-constant authenticated saved-primal shape missing')
            ordered.append(seed_shapes[saved_ref])
        k = len(scope.ranks)
        sh = ordered[0]['shape'] if ordered else []
        if (len(sh) != 3 or any(type(x) is not int or x <= 0 for x in sh)
                or not k or sh[2] % k or len(ordered) != k
                or any(not _same_typed(p['shape'], sh) for p in ordered)):
            raise ValueError('bw-constant equal rank3 sender shapes and exact hidden partition required')
        b, s, full_o = sh
        o = full_o // k
        out, = view.node_outputs(node)
        target = [b, s * k, o]
        name = f"backwardConstant_pm_{row['source_index']}"
        deps = [p['theorem'] for p in ordered]
        seeded = row['theorems'][1]
        proof += [f'theorem {name} (s t : Store) (hi : pmSeededPrefixInitShapes s)',
                  '    (hrun : pmSeededDenoteWithInputs s = some t) :',
                  f'    t {out.tid} = sourceConstantCotangent {target} (1 : Scalar) := by',
                  f'  rw [{seeded} s t hrun]',
                  '  rw [' + ', '.join(f'{d} s t hi hrun' for d in dict.fromkeys(deps)) + ']',
                  f'  exact source_constant_alltoall12_rank3 {k} {b} {s} {o} {scope.local_index} 1',
                  '    (by decide) (by decide) (by decide) (by decide) (by decide)',
                  f'#print axioms {name}']
        rows.append(dict(source_index=row['source_index'], tid=out.tid,
                         ref=list(view.source_tensor(out)), shape=target,
                         ranks=list(scope.ranks), seed_dependency=seeded,
                         shape_dependencies=deps, theorem=name))
    return '\n'.join(proof) + '\n', dict(reads=rows, proof_admissible=False,
        kernel_value_proved=False, public_complete=False, torch_refinement=False)
