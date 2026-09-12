from pathlib import Path


def test_division_joint_witness_contract():
    p=Path(__file__).resolve().parents[2]/'iroha-tasks/trainverify-backward/DivReadWitness.lean'
    assert p.exists(), 'missing original scalar division joint witness'
    text=p.read_text()
    for name in ('caller_nonvacuous','pointwise_derivative','not_cotangent','not_saved','not_multiply'):
        assert name in text
    assert not any(s in text for s in ('sorry','native_decide','axiom '))
