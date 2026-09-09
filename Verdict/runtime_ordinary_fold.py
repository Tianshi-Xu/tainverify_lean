"""Compact totality certificates for fully admitted ordinary request worlds.

This proves success of the existing stepWithInputs fold, not tensor domains,
Torch refinement, initial-parameter agreement, or cross-world value equality.
"""


def render(label, view, world, loaders, *, structured=False, seeded=False):
    from Verdict.runtime_prefix import ProofGroup, _HEADER, _FOOTER
    from Verdict.runtime_world import COLLECTIVES
    order = world.receipt['execution_order'][label]['execution_to_source']
    feeds = {r['index']: r for r in loaders if r['world'] == label}
    missing = {r['index'] for r in world.receipt['missing'] if r['world'] == label}
    # Only canonical ordinary requests and authenticated loaders are total here.
    # A rejected request/collective cannot become an applyNode fallback.
    if (not order or any(str(view.node_opname(view.nodes()[i])).split('.')[-1] in COLLECTIVES
                         or (i in missing and i not in feeds) for i in order)):
        return '', dict(status='prefix-proof-unavailable', reason='no-state-dependent-boundary')
    stem = label + ('SeededWhole' if seeded else 'Whole')
    advance = f'(fun row s => stepWithInputs {label}Graph ({label}Scope row.1) ({label}Peers row.1) s row.1 row.2)'
    initial = f'({label}InitialWithSeeds init)' if seeded else 'init'
    denote = label + ('SeededDenoteWithInputs' if seeded else 'DenoteWithInputs')
    groups = []; names = []
    def group(text, count, final=False):
        groups.append(ProofGroup(text, count, (), final))
    def theorem(name, statement, proof):
        names.append(name)
        return f'theorem {name} {statement} := {proof}\n#print axioms {name}\n'
    total = stem + 'Advance'
    group(f'def {total} (s : Store) (row : InputRequest) : Store :=\n'
          '  match row.2 with\n'
          f'  | none => applyNode {label}Graph s row.1\n'
          '  | some feed => storeSet s feed\n', 1)
    group(theorem(stem+'Fold',
        f'(rows : List InputRequest)\n'
        f'    (h : ∀ row ∈ rows, ∀ s, {advance} row s = some ({total} s row)) (s : Store) :\n'
        f'    runUsing {advance} rows (some s) = some (rows.foldl {total} s)',
        'by\n  induction rows generalizing s with\n'
        '  | nil => rfl\n'
        '  | cons row rest ih =>\n'
        f'    change runUsing {advance} rest ({advance} row s) = _\n'
        '    rw [h row (List.mem_cons_self ..) s]\n'
        '    exact ih (fun next hn => h next (List.mem_cons_of_mem _ hn)) _'), 1)
    for i in order:
        node = f'{label}Node_{i}'
        feed = f'some {node}_feed' if i in feeds else 'none'
        proof = f'{node}_scoped_step s' if i in feeds else 'by\n  change some (applyNode _ _ _) = _\n  rfl'
        group(theorem(stem+f'Step_{i}',
            f'(s : Store) : stepWithInputs {label}Graph ({label}Scope {node}) ({label}Peers {node}) s {node} ({feed}) =\n'
            f'    some ({total} s ({node}, {feed}))', proof), 1)
    group(theorem(stem+'Steps',
        f'(row : InputRequest) (h : row ∈ {label}InputRequests) (s : Store) :\n'
        f'    {advance} row s = some ({total} s row)',
        f'by\n  simp only [{label}InputRequests, List.mem_cons, List.not_mem_nil, or_false] at h\n'
        '  rcases h with ' + ' | '.join('rfl' for _ in order) + '\n' +
        '\n'.join(f'  · exact {stem}Step_{i} s' for i in order)), 1)
    group(f'def {stem}State (init : Store) : Store := {label}InputRequests.foldl {total} {initial}\n', 1)
    run = theorem(stem+'Run', f'(init : Store) : runUsing {advance} {label}InputRequests (some {initial}) = some ({stem}State init)',
                  f'{stem}Fold {label}InputRequests {stem}Steps {initial}')
    proof = ('by\n' + (f'  unfold {label}SeededDenoteWithInputs\n' if seeded else '') +
             f'  rw [{label}DenoteWithInputs_entry]\n  exact {stem}Run init')
    success = theorem(stem+'Success', f'(init : Store) : {denote} init = some ({stem}State init)', proof)
    frame = theorem(stem+'Frame',
        f'(init : Store) (tid : Tid) (h : ∀ row ∈ {label}InputRequests, tid ∉ row.1.outs) :\n'
        f'    ({stem}State init) tid = {initial} tid',
        f'SourceScopedPrefix.frame {label}Graph {label}Scope {label}Peers _ {initial} ({stem}State init) tid h ({stem}Run init)')
    group(run+success+frame, 3, final=True)
    text = groups if structured else _HEADER + '\n'.join(g.text for g in groups) + _FOOTER
    return text, dict(status='ordinary-fold-emitted', prefix_nodes=order, prefix_length=len(order),
        frontier=None, kernel_checks=names, kernel_checked=False, whole_world_option_success=False,
        tensor_domain_refinement=False, external_adapter_proved=False)
