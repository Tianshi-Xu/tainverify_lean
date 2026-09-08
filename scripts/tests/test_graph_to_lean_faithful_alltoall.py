"""Faithful route heldouts, including the generated single-fold consumer."""
import unittest
from Verdict import graph_to_lean as c
from scripts.tests.test_graph_to_lean_collective_scope import fixture, bind_adapters


def same_axis(ranks=(0, 2), axis=0, forward=True):
    g,s=fixture(ranks=ranks,forward=forward)
    for n in g.ns[1::2]:
        g.kw[n].update(idim=axis,odim=axis)
        g.shapes[g.outs[n][0]]=g.shapes[g.ins[n][0]]
    for w in s['writers']:
        if 'adapter_kwargs' in w: w['adapter_kwargs'].update(idim=axis,odim=axis)
    for row in s['adapter_source']:
        if 'primitive' in row: row['primitive']['kwargs'].update(idim=axis,odim=axis)
    bind_adapters(s)
    return g,s

class FaithfulTests(unittest.TestCase):
    def test_generated_certificate_composes_in_one_mixed_fold(self):
        g,s=same_axis();v,=c._lower_runtime_graphs(g);c.attach_collective_scopes(v,s)
        text=c.emit_collective_scope_certificates(v)
        self.assertIn('theorem collective_1_fold',text)
        self.assertIn('SourceScopedEval.run_cons',text)
        self.assertIn('collective_1 g s hworld',text)
        self.assertNotIn('AllToAllSourceFaithful.run',text)

    def test_mixed_witness_generation_is_portable_and_deterministic(self):
        text = mixed_witness()
        self.assertEqual(text, mixed_witness())
        self.assertIn('nodes := [ag0,ag2,aa,ident]', text)
        self.assertIn('collective_1_fold graph s2', text)
        self.assertIn('SourceScopedEval.denote graph scope peers initial', text)
        self.assertIn('#print axioms mixed_value', text)

    def test_heldout_same_axes_bw_and_noncontiguous_groups(self):
        for ranks in ((1,4),(0,2,5)):
            for axis in (0,1,-1):
                for forward in (True,False):
                    with self.subTest(ranks=ranks,axis=axis,forward=forward):
                        g,s=same_axis(ranks,axis,forward)
                        v,=c._lower_runtime_graphs(g);c.attach_collective_scopes(v,s)
                        text=c.emit_collective_scope_certificates(v)
                        self.assertEqual(text,c.emit_collective_scope_certificates(v))
                        self.assertEqual(len(v.collective_scopes),len(ranks))
                        self.assertTrue(all(not x.proof_admissible for x in v.collective_scopes.values()))
                        self.assertNotIn('evalOp ',text)



def mixed_witness():
    """One generated certificate consumed inside AG→AG→A2A→identity fold."""
    g,s=same_axis()
    for t in g.ts: g.shapes[t]=(2,)
    v,=c._lower_runtime_graphs(g);c.attach_collective_scopes(v,s)
    return c.emit_collective_scope_certificates(v) + MIXED_VALUE_WITNESS

MIXED_VALUE_WITNESS = """
namespace TrainVerify.Denote.MixedWitness
set_option maxHeartbeats 500000
noncomputable section
open CollectiveCompiler
def ag0 : NodeDecl := {rank := 0, op := "OpName.AllGatherPrim", ins := [100,101], outs := [0], params := [0]}
def ag2 : NodeDecl := {rank := 2, op := "OpName.AllGatherPrim", ins := [100,101], outs := [2], params := [0]}
def aa : NodeDecl := {rank := 0, op := "OpName.AllToAllPrim", ins := [0,2], outs := [1], params := [0,0]}
def ident : NodeDecl := {rank := 0, op := "OpName.FW_contiguous", ins := [1], outs := [200], params := []}
def graph : GraphDecl := {numRanks := 4, nodes := [ag0,ag2,aa,ident]}
def scope (n : NodeDecl) : GroupScopedEval.Request := if n.op = "OpName.FW_contiguous" then .global else .group (some [0,2])
def peers (_ : NodeDecl) : Nat → Tid := peer_1
def initial : Store := fun tid => ⟨[1], fun _ => if tid = 100 then 1 else 2⟩
def a : Tensor := allGatherPrimDimN 0 2 0 [initial 100, initial 101]
def s1 : Store := storeSet initial [(0,a)]
def s2 : Store := storeSet s1 [(2,a)]
theorem mixed_value : ∃ final, SourceScopedEval.denote graph scope peers initial = some final ∧
    valAt (final 200) 1 = 1 := by
  have h0 : SourceScopedEval.step graph (scope ag0) (peers ag0) initial ag0 = some s1 := by
    change SourceScopedEval.step graph (.group (some [0,2])) _ _ _ = _
    rw [SourceScopedEval.step_group _ _ _ _ _ (by decide) (by decide)]
    exact GroupScopedEval.step_scoped graph initial ag0 [0,2] (by decide) (by rfl)
  have h2 : SourceScopedEval.step graph (scope ag2) (peers ag2) s1 ag2 = some s2 := by
    change SourceScopedEval.step graph (.group (some [0,2])) _ _ _ = _
    rw [SourceScopedEval.step_group _ _ _ _ _ (by decide) (by decide)]
    exact GroupScopedEval.step_scoped graph s1 ag2 [0,2] (by decide) (by rfl)
  obtain ⟨s3, hrun, hout⟩ := collective_1_fold graph s2 rfl (by rfl) (by rfl) scope peers rfl rfl [ident]
  refine ⟨applyNode graph s3 ident, ?_, ?_⟩
  · change SourceScopedEval.run graph scope peers [ag0,ag2,aa,ident] (some initial) = _
    rw [SourceScopedEval.run_cons, h0, SourceScopedEval.run_cons, h2]
    change SourceScopedEval.run graph scope peers [aa,ident] (some s2) = _
    unfold aa
    rw [hrun, SourceScopedEval.run_cons]
    change SourceScopedEval.run graph scope peers [] (SourceScopedEval.step graph .global _ _ ident) = _
    rw [SourceScopedEval.step_global _ _ _ _ (by rfl)]
    rfl
  · change valAt (s3 1) 1 = 1
    rw [hout]
    norm_num [s2, s1, a, initial, storeSet, allGatherPrimDimN, chunkPrimDimN,
      valAt, Tensor.mkShape, prodShape, List.getD]
    rfl
#print axioms mixed_value
end
end TrainVerify.Denote.MixedWitness
"""

if __name__=='__main__': unittest.main()
