"""Recorder behavior is tested independently of costly public reauthentication."""
import importlib.util
from types import SimpleNamespace
import pytest


def api():
    assert importlib.util.find_spec('trainverify.frontier_replay'), 'versioned replay driver missing'
    from trainverify import frontier_replay
    return frontier_replay


def chain(mode='valid'):
    detail=dict(proof_admissible=False,kernel_value_proved=False,public_complete=False,torch_refinement=False,
        reads=[],units=[],frontier_units=[],retained_units=[],deferred_units=[])
    base=SimpleNamespace(__name__='Verdict.runtime_fixture_base',render=lambda *six:('base text\n',detail))
    def render(*six):
        passed=six if mode!='copied-input' else (*six[:2],dict(six[2]),*six[3:])
        base.render(*passed)
        if mode=='duplicate': base.render(*six)
        return 'target text\n',dict(detail)
    target=SimpleNamespace(__name__='Verdict.runtime_fixture_target',predecessor=base,render=render)
    records=[dict(module=base.__name__,name='FixtureBase',imports=['RuntimeWorld'],detail='base')]
    final=dict(module=target.__name__,name='FixtureTarget',imports=['FixtureBase'])
    six=(object(),object(),{},object(),object(),object())
    return target,records,final,six,base


def test_public_context_records_same_six_and_restores(tmp_path):
    subject=api(); target,records,final,six,base=chain(); original=base.render
    result=subject.render_context(target,records,final,tmp_path,*six)
    assert base.render is original
    assert result['predecessor_public_calls']=={'FixtureBase':1}
    assert (tmp_path/'FixtureBase.lean').read_text()=='import RuntimeWorld\nbase text\n'
    assert (tmp_path/'FixtureTarget.lean').read_text()=='import FixtureBase\ntarget text\n'
    assert result['detail']['proof_admissible'] is False


@pytest.mark.parametrize('mode',['copied-input','duplicate'])
def test_bad_public_calls_do_not_emit_and_restore(tmp_path,mode):
    subject=api(); target,records,final,six,base=chain(mode); original=base.render
    with pytest.raises(ValueError): subject.render_context(target,records,final,tmp_path,*six)
    assert base.render is original and list(tmp_path.iterdir())==[]


def test_wrong_module_labels_do_not_emit(tmp_path):
    subject=api(); target,records,final,six,_=chain()
    records[0]['module']='Verdict.runtime_other'
    with pytest.raises(ValueError): subject.render_context(target,records,final,tmp_path,*six)
    assert list(tmp_path.iterdir())==[]
