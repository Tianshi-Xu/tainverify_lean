"""Retire path aliases only after complete, identity-preserving link rewrites."""
import importlib.util
import json
import os
from pathlib import Path

import pytest
from scripts.tests.test_artifact_tools import fixture


def setup(tmp_path):
    from trainverify.artifact_tools import Configuration
    path,_,old,store=fixture(tmp_path)
    old.symlink_to(store,target_is_directory=True)
    cache=tmp_path/'cache'; cache.mkdir()
    (cache/'object.olean').symlink_to(old/'object.bin')
    return Configuration.load(path),old,store,cache


def api():
    assert importlib.util.find_spec('trainverify.artifact_links'), 'versioned link migration missing'
    from trainverify import artifact_links
    return artifact_links


def test_complete_rewrite_then_remove_alias(tmp_path):
    subject=api(); config,old,store,cache=setup(tmp_path)
    plan=subject.plan_links(config,[cache])
    assert len(plan['links'])==1
    subject.apply_links(config,plan)
    assert os.readlink(cache/'object.olean')==str(store/'object.bin')
    assert old.is_symlink()
    result=subject.remove_aliases(config,[cache])
    assert result['removed_aliases']==1 and not old.is_symlink() and not old.exists()
    assert (cache/'object.olean').read_bytes()==b'checked object bytes'
    assert config.verify()['files_verified']==1


def test_remaining_old_reference_blocks_alias_removal(tmp_path):
    subject=api(); config,old,_,cache=setup(tmp_path)
    with pytest.raises(ValueError,match='references'):
        subject.remove_aliases(config,[cache])
    assert old.is_symlink()


@pytest.mark.parametrize('fault',['omission','target','duplicate','replacement'])
def test_invalid_plan_is_zero_write(tmp_path,fault):
    subject=api(); config,old,_,cache=setup(tmp_path)
    plan=subject.plan_links(config,[cache]); p=cache/'object.olean'; target=os.readlink(p)
    if fault=='omission': plan['links']=[]
    elif fault=='target': plan['links'][0]['new_target']=str(tmp_path/'elsewhere')
    elif fault=='duplicate': plan['links']*=2
    else:
        p.unlink(); p.write_text('foreign replacement')
    with pytest.raises(ValueError): subject.apply_links(config,plan)
    assert old.is_symlink()
    if fault=='replacement': assert p.read_text()=='foreign replacement'
    else: assert os.readlink(p)==target


def test_git_metadata_links_are_not_silently_omitted(tmp_path):
    subject=api(); config,old,_,cache=setup(tmp_path)
    metadata=cache/'.git'; metadata.mkdir()
    (metadata/'hook').symlink_to(old/'object.bin')
    plan=subject.plan_links(config,[cache])
    assert {r['path'] for r in plan['links']}=={str(cache/'object.olean'),str(metadata/'hook')}


def test_plan_cannot_include_unrelated_noop_replacement(tmp_path):
    subject=api(); config,old,store,cache=setup(tmp_path)
    plan=subject.plan_links(config,[cache])
    unrelated=cache/'unrelated'; unrelated.symlink_to(store/'object.bin')
    row=dict(plan['links'][0],path=str(unrelated),old_target=str(store/'object.bin'),new_target=str(store/'object.bin'))
    s=unrelated.lstat(); row['link_identity']=[s.st_dev,s.st_ino,row['link_identity'][2]]
    plan['links'].append(row)
    with pytest.raises(ValueError): subject.apply_links(config,plan)
    assert old.is_symlink() and os.readlink(cache/'object.olean')==str(old/'object.bin')
    assert unrelated.lstat().st_ino==s.st_ino


def test_unrelated_noncanonical_target_is_preserved(tmp_path):
    subject=api(); config,_,store,cache=setup(tmp_path)
    (store/'sub').mkdir()
    target=str(store)+'/sub/../object.bin'
    (cache/'other').symlink_to(target)
    plan=subject.plan_links(config,[cache])
    assert len(plan['links'])==1 and os.readlink(cache/'other')==target


def test_legacy_dotdot_target_maps_only_same_referent(tmp_path):
    subject=api(); config,old,store,cache=setup(tmp_path)
    (store/'sub').mkdir()
    target=str(old)+'/sub/../object.bin'
    (cache/'other').symlink_to(target)
    plan=subject.plan_links(config,[cache]); subject.apply_links(config,plan)
    assert len(plan['links'])==2 and os.readlink(cache/'other')==str(store/'object.bin')
    assert next(r for r in plan['links'] if r['path']==str(cache/'other'))['old_target']==target


def test_partial_failure_can_resume_without_rollback(tmp_path,monkeypatch):
    subject=api(); config,old,store,cache=setup(tmp_path)
    (cache/'second.olean').symlink_to(old/'object.bin')
    plan=subject.plan_links(config,[cache]); original=os.replace; count=0
    def fail_second(*args,**kwargs):
        nonlocal count
        count+=1
        if count==2: raise OSError('injected rename failure')
        return original(*args,**kwargs)
    with monkeypatch.context() as m:
        m.setattr(subject.os,'replace',fail_second)
        with pytest.raises(OSError): subject.apply_links(config,plan)
    assert old.is_symlink() and all(p.read_bytes()==b'checked object bytes' for p in cache.iterdir())
    subject.apply_links(config,plan)
    subject.remove_aliases(config,[cache])
    assert not old.exists() and all(os.readlink(p)==str(store/'object.bin') for p in cache.iterdir())
