"""Direct Lean checks with pinned artifacts and exact query inventories."""
import importlib.util
from pathlib import Path
import sys
import pytest
from scripts.tests.test_artifact_tools import fixture,sha


def api():
    assert importlib.util.find_spec('trainverify.artifact_lean'), 'versioned Lean checker missing'
    from trainverify import artifact_lean
    return artifact_lean


def test_first_namespace_does_not_fall_back(tmp_path):
    subject=api(); first=tmp_path/'first'; second=tmp_path/'second'
    (first/'denote').mkdir(parents=True); (second/'denote').mkdir(parents=True)
    (second/'denote/Target.olean').write_bytes(b'other root')
    with pytest.raises(ValueError,match='namespace'):
        subject.resolve_import('denote.Target',[first,second])
    expected=first/'denote/Target.olean'; expected.write_bytes(b'first root')
    assert subject.resolve_import('denote.Target',[first,second])==expected


def test_exact_axiom_query_inventory():
    subject=api()
    text="'Demo.first' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Demo.second' does not depend on any axioms\n"
    assert subject.parse_axioms(text,['Demo.first','Demo.second'])=={
        'Demo.first':['propext','Classical.choice','Quot.sound'],'Demo.second':[]}


@pytest.mark.parametrize('text',[
    "'Demo.first' depends on axioms: [sorryAx]\n",
    "'Demo.first' depends on axioms: [propext, propext]\n",
    "'Demo.first' does not depend on any axioms\n'Demo.first' does not depend on any axioms\n",
    "'Demo.other' does not depend on any axioms\n",
    "warning: ignored\n'Demo.first' does not depend on any axioms\n",
])
def test_invalid_axiom_queries_fail_closed(text):
    with pytest.raises(ValueError): api().parse_axioms(text,['Demo.first'])


def test_bad_source_cannot_create_output(tmp_path):
    subject=api()
    from trainverify.artifact_tools import Configuration
    _,data,_,store=fixture(tmp_path)
    data['lean']=dict(executable=sys.executable,sha256=sha(Path(sys.executable).read_bytes()),paths=[str(store)])
    config=Configuration(data)
    source=tmp_path/'input.lean'; source.write_text('import Missing\n#print axioms Demo.first\n')
    output=tmp_path/'must-not-exist'
    with pytest.raises(ValueError,match='source hash'):
        subject.run_lean(config,str(source),'0'*64,output,['Demo.first'])
    assert not output.exists()
