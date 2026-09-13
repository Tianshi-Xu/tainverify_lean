"""Portable artifact tools: no dependency on old working-directory aliases."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys


def sha(data):
    return hashlib.sha256(data).hexdigest()


def fixture(tmp_path):
    old=tmp_path/'gone-worktree'; store=tmp_path/'evidence'; store.mkdir()
    data=b'checked object bytes'; (store/'object.bin').write_bytes(data)
    bindings=tmp_path/'bindings.json'
    bindings.write_text(json.dumps({str(old/'object.bin'):sha(data)}))
    config=dict(version=1,relocations=[dict(kind='directory',source=str(old),target=str(store))],
        binding_sets=[dict(path=str(bindings),sha256=sha(bindings.read_bytes()),field=[],base=None)],lean=None)
    path=tmp_path/'layout.json'; path.write_text(json.dumps(config))
    return path,config,old,store


def test_public_verify_without_legacy_directory(tmp_path):
    assert importlib.util.find_spec('trainverify.artifact_tools'), 'versioned artifact tooling missing'
    from trainverify.artifact_tools import Configuration
    path,_,old,store=fixture(tmp_path)
    config=Configuration.load(path)
    assert not old.exists() and config.resolve(str(old/'object.bin'))==store/'object.bin'
    result=tmp_path/'result.json'
    run=subprocess.run([sys.executable,'-m','trainverify.artifact_tools','verify','--config',str(path),
        '--output',str(result)],capture_output=True,text=True,
        env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1'))
    assert run.returncode==0,run.stdout+run.stderr
    report=json.loads(result.read_text())
    assert report['status']=='verified' and report['files_verified']==1
    assert report['proof_admissible'] is False
    assert not old.exists()


def test_joint_builder_keeps_full_mixed_contracts():
    from trainverify import artifact_tools as subject
    assert hasattr(subject,'render_joint'), 'versioned joint builder missing'
    base=dict(sm_output_tid=10,pm_output_tids=[20,21],dimensions=dict(D=2,T=2),unit=0,
        global_shape=[2,4],local_shape=[1,2],gather_axis=1,layout='sharded',facts_theorem='scoreFacts')
    replica=dict(base,pm_output_tids=[30,31],local_shape=[1,4],gather_axis=None,
        layout='replicated_within_dp',facts_theorem='replicaFacts')
    text=subject.render_joint([base,replica],'FreshScoreExchange')
    assert '(t 10).shape = [2, 4]' in text and 'y.shape = [1, 2]' in text
    assert 'allGatherPrimDimN 1 2 0 [q 20, q 21]' in text
    assert '(∀ y ∈ [q 30, q 31], y = chunkPrimDimN 0 2 0 (t 10))' in text
    assert text.count('InitialParameterValues s p')==1
    assert 'scoreFacts s p t q hs hp hvalues' in text
    assert 'replicaFacts s p t q hs hp hvalues' in text


def test_changed_payload_rejected_without_clobber(tmp_path):
    from trainverify.artifact_tools import Configuration
    path,_,_,store=fixture(tmp_path)
    (store/'object.bin').write_bytes(b'wrong')
    output=tmp_path/'sentinel.json'; output.write_text('keep')
    run=subprocess.run([sys.executable,'-O','-m','trainverify.artifact_tools','verify',
        '--config',str(path),'--output',str(output)],capture_output=True,text=True)
    assert run.returncode!=0 and 'hash mismatch' in run.stdout
    assert output.read_text()=='keep'


def test_kernel_receipt_verification_uses_layout(tmp_path):
    from trainverify import artifact_tools as subject
    assert hasattr(subject,'verify_kernel'), 'versioned kernel receipt checker missing'
    path,_,old,store=fixture(tmp_path)
    source=b'theorem demo : True := True.intro\n'
    (store/'demo.lean').write_bytes(source)
    receipt=dict(source=str(old/'demo.lean'),source_sha256=sha(source),object=str(old/'object.bin'),
        object_sha256=sha((store/'object.bin').read_bytes()),inner_exit=0,
        axioms={'Demo.demo':['propext']},dependency_objects={str(old/'object.bin'):sha((store/'object.bin').read_bytes())})
    f=tmp_path/'kernel.json'; f.write_text(json.dumps(receipt))
    result=subject.verify_kernel(subject.Configuration.load(path),str(f),sha(f.read_bytes()))
    assert result['checked_declarations']==1 and result['proof_admissible'] is False
