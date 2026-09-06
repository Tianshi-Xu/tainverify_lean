"""Synthetic adapter graph + literal capture metadata, through the real loader.

Not a GPU capture. The existing hidden-sharded embedding→AllToAll test graph is
serialized, its adapter kwargs pass through the real metadata exporter, and the
ordinary whole-model parser/planners/public renderer consume the emitted files.
"""
from pathlib import Path

from Verdict import graph_to_lean as exporter
from Verdict.tests.test_adapter_communication_authority import SyntheticGraph, Tensor
from scripts.tests.test_proof_compiler import _hidden_embedding_alltoall_ir
from trainverify.bridge_emitter import composer, parser
from trainverify.bridge_emitter.model_authority import load_model_authority


def write_fixture(root: Path):
    root = Path(root)
    directory = root / "Fixture"
    directory.mkdir(parents=True, exist_ok=True)
    ir = _hidden_embedding_alltoall_ir()
    records = []
    for rank in (0, 1):
        graph = SyntheticGraph(ranks=(0, 1), inputs=[Tensor(0, 301), Tensor(1, 302)], outputs=[Tensor(rank, 401 + rank)])
        graph.node.rank, graph.node.op = rank, "OpName.AllToAllPrim"
        records.extend(exporter.derive_adapter_communications(graph, graph.nodes))
    lines = ["import denote.RelationCompiler", "open TrainVerify.Denote", "namespace AdapterFixture", "noncomputable section"]
    for side in ("sm", "pm"):
        lines += [f"def {side} : GraphDecl := {{ numRanks := {getattr(ir, side + '_num_ranks')}, nodes := ["
                  + ", ".join(composer._node_text(n) for n in getattr(ir, side + "_nodes")) + "] }",
                  f"def {side}InitShapes : List (Tid × Shape) := " + repr(getattr(ir, side + "_shapes")),
                  f"def {side}InitEnv : ShapeEnv := shapeEnvOfList {side}InitShapes"]
        rows = records if side == "pm" else []
        lines += [f"def {side}AdapterCommunications : List (Nat × Nat × String × List Nat × List (Nat × Nat)) := "
                  + exporter._lean_adapter_communications(rows)]
    def lineage(g):
        pieces = ", ".join(f"{{ rank := {r}, tid := {t} }}" for r, t in g.tps)
        return (f"{{ ts := {g.ts}, tsShape := {g.tsShape}, tps := [{pieces}], "
                f"tpShapes := {g.tpShapes}, gatherDim := {g.gatherDim or 0} }}")
    lines += [f"def initGoal_{tid} : LineageGoal := {lineage(g)}" for tid, g in ir.init_lineages.items()]
    lines += ["def initGoals : List LineageGoal := [initGoal_100, initGoal_101]",
              f"def goal_7 : LineageGoal := {lineage(ir.lineage)}",
              "def externalContract (_sm _pm : Store) : Prop := True",
              "def goal_7_stmt : Prop := CoarseLineageHoldsWithInitDistributedFaithfulWithContract sm pm goal_7 smInitEnv pmInitEnv initGoals externalContract",
              "end", "end AdapterFixture", ""]
    (directory / "GeneratedData.lean").write_text("\n".join(lines))
    (directory / "AllGoalsFull.lean").write_text(
        "import Fixture.GeneratedData\nnamespace AdapterFixture\n"
        "def all_goals_stmt_full : Prop := goal_7_stmt\nend AdapterFixture\n")
    (directory / "Witness.lean").write_text(WITNESS)
    settings = {name: getattr(parser, name) for name in ("DENOTE_DIR", "GEN_DIR", "GEN_FILE", "MOD_PREFIX")}
    try:
        parser.DENOTE_DIR = parser.GEN_DIR = "Fixture"
        parser.GEN_FILE, parser.MOD_PREFIX = "GeneratedData.lean", "Fixture"
        return load_model_authority((7,), str(root), model_id="adapter-fixture", allow_partial=False)
    finally:
        for name, value in settings.items():
            setattr(parser, name, value)


WITNESS = '''import Fixture.GeneratedData
import denote.GraphGears
import AdapterProof.Main
open TrainVerify.Denote TrainVerify.Denote.RelationCompiler
namespace AdapterFixture
noncomputable section
def tokens : Tensor := Tensor.mkShape [8] (fun i => (i.val : Nat))
def weight : Tensor := Tensor.mkShape [16, 4] (fun i => (i.val + 1 : Nat))
def w0 := chunkPrimDimN 1 2 0 weight
def w1 := chunkPrimDimN 1 2 1 weight
theorem weight_sharded : ShardedRel weight [w0, w1] 1 [16, 4] [16, 2] :=
  ShardedRel.of_chunks_two rfl rfl rfl (by decide) rfl rfl rfl
def initSM : Store := fun tid => if tid = 100 then tokens else if tid = 101 then weight else zeroTensor []
def initPM : Store := fun tid => if tid = 100 then tokens else if tid = 201 then w0 else if tid = 202 then w1 else zeroTensor []
theorem publicInputs : StoreShapesHold initSM smInitEnv ∧ StoreShapesHold initPM pmInitEnv ∧
    InitGoalsHold 2 initGoals initSM initPM ∧ externalContract initSM initPM := by
  refine ⟨?_, ?_, ?_, trivial⟩
  · intro tid sh h
    have hm := shapeEnvOfList_mem_of_eq_some h
    simp only [smInitShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · intro tid sh h
    have hm := shapeEnvOfList_mem_of_eq_some h
    simp only [pmInitShapes, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  · intro g hg
    simp only [initGoals, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact ⟨rfl, rfl, rfl⟩
    · refine ⟨rfl, rfl, ?_⟩
      rw [reconstructForGoal_of_not_replicated _ _ _ rfl]
      change weight = reconstructWithDim 1 2 0 [w0, w1]
      rw [reconstructWithDim_cons_cons_nonscalar 1 2 0 w0 w1 [] (by decide)]
      exact weight_sharded.full_value
theorem inhabitedOutput : InitGoalHolds 2 goal_7
    (denoteGraphDistributedFaithful sm initSM) (denoteGraphDistributedFaithful pm initPM) := by
  exact TrainVerify.Denote.AdapterProof.all_outputs initSM initPM
    publicInputs.1 publicInputs.2.1 publicInputs.2.2.1 publicInputs.2.2.2
#print axioms publicInputs
#print axioms inhabitedOutput
end
end AdapterFixture
'''
