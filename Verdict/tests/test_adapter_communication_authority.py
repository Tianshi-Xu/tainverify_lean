"""Synthetic graph fixtures; no torch, nnScaler import, or GPU capture."""
from dataclasses import dataclass, FrozenInstanceError
from types import SimpleNamespace
import pytest
from Verdict import graph_to_lean as exporter


@dataclass(frozen=True)
class Tensor:
    rank: int
    tid: int


@dataclass(eq=False)
class Node:
    rank: int = 2
    op: str = "OpName.AllReducePrim"


class SyntheticGraph:
    """Explicit synthetic implementation of the captured graph accessors."""
    def __init__(self, *, ranks=(2, 0), inputs=None, outputs=None, kwargs=None):
        self.node = Node()
        self.nodes = [self.node]
        self.kwargs = {"ranks": ranks} if kwargs is None else kwargs
        self.inputs = [Tensor(2, 20), Tensor(0, 10)] if inputs is None else inputs
        self.outputs = [Tensor(2, 30)] if outputs is None else outputs

    def node_opname(self, node): return node.op
    def node_kwargs(self, node): return self.kwargs
    def node_inputs(self, node): return self.inputs
    def node_outputs(self, node): return self.outputs


def test_source_group_order_and_frozen_record():
    graph = SyntheticGraph()
    assert hasattr(exporter, "derive_adapter_communications")
    records = exporter.derive_adapter_communications(graph, graph.nodes)
    assert records == [exporter.AdapterCommunication(2, 30, "AllReducePrim", (2, 0), ((2, 20), (0, 10)))]
    with pytest.raises(FrozenInstanceError):
        records[0].rank = 1


@pytest.mark.parametrize("op", ["AllToAllPrim", "AllGatherPrim", "AllReducePrim", "ReduceScatterPrim"])
def test_primitive_families(op):
    graph = SyntheticGraph()
    graph.node.op = "OpName." + op
    assert exporter.derive_adapter_communications(graph, graph.nodes)[0].op == op


@pytest.mark.parametrize("kwargs", [{}, {"ranks": None}, {"ranks": []}, {"ranks": [2, 2]},
    {"ranks": [2, True]}, {"ranks": [2, -1]}, {"ranks": [2, "0"]}, {"ranks": {2, 0}}])
def test_invalid_or_missing_group(kwargs):
    graph = SyntheticGraph(kwargs=kwargs)
    with pytest.raises(ValueError, match="ranks"):
        exporter.derive_adapter_communications(graph, graph.nodes)


def test_node_rank_not_in_group():
    graph = SyntheticGraph(ranks=(1, 0), inputs=[Tensor(1, 20), Tensor(0, 10)])
    with pytest.raises(ValueError, match="node rank"):
        exporter.derive_adapter_communications(graph, graph.nodes)


@pytest.mark.parametrize("inputs", [[], [Tensor(2, 20)], [Tensor(2, 20), Tensor(2, 21)],
    [Tensor(0, 10), Tensor(2, 20)],  # permutation: never silently repair by sorting
    [Tensor(2, 20), Tensor(1, 10)],  # independent equal-count wrong group
    [Tensor(2, 20), Tensor(0, 10), Tensor(0, 11)],  # multi-input per rank
    [SimpleNamespace(tid=20), Tensor(0, 10)], [Tensor(True, 20), Tensor(0, 10)]])
def test_reject_unfaithful_fused_ownership(inputs):
    graph = SyntheticGraph(inputs=inputs)
    with pytest.raises(ValueError, match="input"):
        exporter.derive_adapter_communications(graph, graph.nodes)


def test_missing_output():
    graph = SyntheticGraph(outputs=[])
    with pytest.raises(ValueError, match="output"):
        exporter.derive_adapter_communications(graph, graph.nodes)


@pytest.mark.parametrize("bad", [True, -1, None, "2"])
def test_invalid_node_rank(bad):
    graph = SyntheticGraph()
    graph.node.rank = bad
    with pytest.raises(ValueError, match="node rank"):
        exporter.derive_adapter_communications(graph, graph.nodes)


@pytest.mark.parametrize("bad", [True, -1, None, "20"])
def test_invalid_tensor_ids(bad):
    for field in ("inputs", "outputs"):
        graph = SyntheticGraph()
        getattr(graph, field)[0] = Tensor(2, bad)
        with pytest.raises(ValueError, match="tid"):
            exporter.derive_adapter_communications(graph, graph.nodes)


def test_non_adapter_never_reads_authority():
    graph = SyntheticGraph(kwargs={}, inputs=[], outputs=[])
    graph.node.op = "OpName.FW_maybe_shuffle"
    assert exporter.derive_adapter_communications(graph, graph.nodes) == []


def test_renderer_core_lean_tuple():
    graph = SyntheticGraph()
    assert hasattr(exporter, "_lean_adapter_communications")
    assert exporter._lean_adapter_communications(exporter.derive_adapter_communications(graph, graph.nodes)) == (
        '[(2, 30, "AllReducePrim", [2, 0], [(2, 20), (0, 10)])]'
    )
    assert exporter._lean_adapter_communications([]) == "[]"


class SyntheticEmissionGraph(SyntheticGraph):
    """Adds shape/init accessors only for exercising the real file emitter."""
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        del self.nodes

    def nodes(self): return [self.node]
    def tensors(self): return self.inputs + self.outputs
    def tensor_shape(self, tensor): return [8]
    def is_initialized(self, tensor): return tensor in self.inputs


def emit_fixture(module, out, *, flag=None, graph=None):
    graph = graph or SyntheticEmissionGraph()
    sm = SyntheticEmissionGraph(ranks=(0,), inputs=[Tensor(0, 1)], outputs=[Tensor(0, 2)])
    sm.node.rank = 0
    out.parent.mkdir(parents=True, exist_ok=True)
    kwargs = {} if flag is None else {"with_adapter_communications": flag}
    module.emit_lean_spec(
        out_path=out, spec_out_path=None, emit_spec_template=False, overwrite_spec=False,
        module_name="Fixture.GeneratedData", sm_nodes=sm.nodes(), pm_nodes=graph.nodes(),
        sm_graph=sm, pm_graph=graph, sm_logical_ids={}, pm_logical_ids={},
        sm_input_value_classes=[], pm_input_value_classes=[], init_goals=[], goals=[], **kwargs,
    )
    return {p.name: p.read_bytes() for p in out.parent.glob("*.lean")}


def test_cli_flag_drives_actual_file_emission(monkeypatch, tmp_path):
    import sys
    monkeypatch.setattr(sys, "argv", ["graph_to_lean.py", "--out", str(tmp_path / "GeneratedData.lean"),
        "--module", "Fixture.GeneratedData", "--with-adapter-communications"])
    args = exporter.parse_args()
    files = emit_fixture(exporter, tmp_path / "enabled" / "GeneratedData.lean", flag=args.with_adapter_communications)
    text = files["GeneratedData.lean"].decode()
    ty = "List (Nat × Nat × String × List Nat × List (Nat × Nat))"
    assert f'def smAdapterCommunications : {ty} := [(0, 2, "AllReducePrim", [0], [(0, 1)])]' in text
    assert f'def pmAdapterCommunications : {ty} := [(2, 30, "AllReducePrim", [2, 0], [(2, 20), (0, 10)])]' in text
    assert "adapterCommunications :=" not in text
    assert text.index("def sm : GraphDecl") < text.index("def smAdapterCommunications") < text.index("def pm : GraphDecl")
    assert text.index("def pm : GraphDecl") < text.index("def pmAdapterCommunications") < text.index("def smInputValueClasses")


def test_disabled_flag_preserves_pinned_legacy_bytes(monkeypatch, tmp_path):
    import subprocess
    import sys
    import types
    from pathlib import Path
    root = Path(exporter.__file__).resolve().parents[1]
    source = subprocess.check_output(["git", "-C", str(root), "show", "084bf17a:Verdict/graph_to_lean.py"], text=True)
    baseline = types.ModuleType("adapter_legacy_exporter")
    baseline.__file__ = exporter.__file__
    monkeypatch.setitem(sys.modules, baseline.__name__, baseline)
    exec(compile(source, exporter.__file__, "exec"), baseline.__dict__)
    expected = emit_fixture(baseline, tmp_path / "baseline" / "GeneratedData.lean")
    assert emit_fixture(exporter, tmp_path / "default" / "GeneratedData.lean") == expected
    assert emit_fixture(exporter, tmp_path / "disabled" / "GeneratedData.lean", flag=False) == expected
    monkeypatch.setattr(sys, "argv", ["graph_to_lean.py", "--out", "unused.lean", "--module", "Fixture.GeneratedData"])
    assert exporter.parse_args().with_adapter_communications is False


def test_enabled_emit_fails_closed_without_publishing(tmp_path):
    graph = SyntheticEmissionGraph(inputs=[Tensor(0, 10), Tensor(2, 20)])
    out = tmp_path / "invalid" / "GeneratedData.lean"
    with pytest.raises(ValueError, match="input ownership"):
        emit_fixture(exporter, out, flag=True, graph=graph)
    assert not out.exists()
    assert not (out.parent / "GeneratedGraphNodes.lean").exists()
    # Legacy generation does not demand adapter authority when opt-in is absent.
    assert emit_fixture(exporter, out, flag=False, graph=graph)


def test_generate_threads_flag_to_real_emitter():
    import ast
    import inspect
    tree = ast.parse(inspect.getsource(exporter._generate))
    calls = [n for n in ast.walk(tree) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)
             and n.func.id == "emit_lean_spec"]
    assert len(calls) == 1
    keyword = next((k for k in calls[0].keywords if k.arg == "with_adapter_communications"), None)
    assert keyword is not None
    assert "with_adapter_communications" in ast.unparse(keyword.value)


def test_pinned_collectiveprim_source_contract():
    """Source-level AST oracle, NOT an imported runtime/GPU capture test."""
    import ast
    import os
    import subprocess
    from pathlib import Path
    root = Path(os.environ.get("TRAINVERIFY_NNSCALER_SOURCE",
        "/home/v-zhouziyu/work/trainverify/.hermes-runs/remote-yoco-release-20260822/upstream/nnscaler"))
    if not root.is_dir():
        pytest.skip("pinned nnScaler source checkout unavailable")
    pin = "d3d468ed23edb2f28aa8566b2dfb6ed49c5955cf"
    assert subprocess.check_output(["git", "-C", str(root), "rev-parse", "HEAD"], text=True).strip() == pin
    path = "nnscaler/ir/adapter/prim.py"
    source = (root / path).read_text()
    assert source == subprocess.check_output(["git", "-C", str(root), "show", f"{pin}:{path}"], text=True)
    classes = {n.name: n for n in ast.parse(source).body if isinstance(n, ast.ClassDef)}
    constructor = next(n for n in classes["CollectivePrim"].body if isinstance(n, ast.FunctionDef) and n.name == "__init__")
    branch = next(n for n in constructor.body if isinstance(n, ast.If))
    assert ast.unparse(branch.test) == "'ranks' not in self.kwargs"
    assert ast.unparse(branch.body[0]) == "self.kwargs['ranks'] = self.device"
    for name in ("AllToAllPrim", "AllGatherPrim", "AllReducePrim", "ReduceScatterPrim"):
        assert [ast.unparse(base) for base in classes[name].bases] == ["CollectivePrim"]
        init = next(n for n in classes[name].body if isinstance(n, ast.FunctionDef) and n.name == "__init__")
        assert any(isinstance(n, ast.keyword) and n.arg is None and ast.unparse(n.value) == "kwargs" for n in ast.walk(init))
