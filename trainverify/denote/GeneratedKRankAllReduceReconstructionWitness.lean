import denote.RelationCompiler

open TrainVerify.Denote
open TrainVerify.Denote.RelationCompiler

namespace TrainVerify.Denote.GeneratedKRankAllReduceReconstructionWitness

noncomputable section

variable (full c0 c1 c2 : Tensor) (shape : Shape)

theorem reduction_api
    (h : ReductionRel full [c0, c1, c2] shape) :
    full = allReducePrim 3 0 [c0, c1, c2] :=
  ReductionRel.to_joined_allReduce h

#print axioms reduction_api

end
end TrainVerify.Denote.GeneratedKRankAllReduceReconstructionWitness
