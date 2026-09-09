"""Canonical initial contract generation must consume bound source targets."""
from Verdict import runtime_initial_relations as initial
from scripts.tests.test_runtime_initial_relations import setup
from Verdict.runtime_world import WorldDefinitions, _proof_bundle
from Verdict.runtime_prefix import ProofGroup, pack_proofs


def world():
    entry, supporting = pack_proofs([[ProofGroup('theorem existing : True := True.intro\n#print axioms existing', 1, ())]])
    supporting['TrainVerifyRuntimeWorldData.lean'] = 'import denote.SourceScopedEval\n'
    return WorldDefinitions(entry, {'proof_admissible': False, 'public_complete': False}, supporting)


def test_bound_initial_relations_are_emitted_in_same_world_entry():
    sm, pm, parameters, lineages, validation = setup()
    original = world()
    assert hasattr(initial, 'attach'), 'canonical initial relation Lean attachment missing'
    result = initial.attach(original, sm, pm, parameters, lineages, validation)
    assert result.supporting_sources == original.supporting_sources
    assert 'theorem existing : True' in result.lean
    assert 'import denote.SourceInitialParameterSpecs\n' in result.lean
    assert 'def InitialParameterValues (initSM initPM : Store) : Prop' in result.lean
    assert 'theorem initialParameterRelations_of_values' in result.lean
    assert result.lean.count('\n.sharded ') == 2
    assert 'SourceInitialParameters.embedding_unit' not in result.lean
    assert result.receipt['initial_relations']['contract_emitted'] is True
    assert result.receipt['initial_relations']['kernel_value_proved'] is False
    assert result.receipt['proof_admissible'] is False
    assert result.receipt['public_complete'] is False
    assert result.receipt['proof_bundle'] == _proof_bundle(result.lean, result.supporting_sources)


def test_replicated_parameters_emit_copy_not_gather_contract():
    sm, pm, parameters, lineages, validation = setup(copies=True)
    assert hasattr(initial, 'attach'), 'canonical initial relation Lean attachment missing'
    result = initial.attach(world(), sm, pm, parameters, lineages, validation)
    assert result.lean.count('\n.replicated ') == 2
    assert 'sharded_of_exact_slices' not in result.lean


def test_forged_targets_cannot_reach_initial_contract_renderer():
    import pytest
    sm, pm, parameters, lineages, validation = setup()
    assert hasattr(initial, 'attach'), 'canonical initial relation Lean attachment missing'
    with pytest.raises(ValueError):
        initial.attach(world(), sm, pm, parameters, lineages[:-1], validation)
