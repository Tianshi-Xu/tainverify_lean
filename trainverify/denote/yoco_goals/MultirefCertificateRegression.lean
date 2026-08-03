/-
Copyright (c) TrainVerify contributors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TrainVerify contributors
-/
import denote.yoco_goals.GeneratedMultirefCertificates

/-!
# Kernel regression for generated faithful-multiref certificates

This small gate exercises all three goal-7747 certificates without importing
the large downstream lineage proof.  It checks that the generated graph facts
are sufficient to derive the exact value-preserving reductions.
-/

namespace TrainVerify.Denote.GeneratedPatterns

open TrainVerify.Denote
open TrainVerify.Denote.Generated

example (init : Store) :
    denoteGraphDistributedFaithful sm init 7747 =
      denoteGraphDistributedFaithful sm init 5060 :=
  denoteGraphDistributedFaithful_multiref sm init multirefCert_sm_7747_7747

example (init : Store) :
    denoteGraphDistributedFaithful pm init 15221 =
      denoteGraphDistributedFaithful pm init 8695 :=
  denoteGraphDistributedFaithful_multiref pm init multirefCert_pm_7747_15221

example (init : Store) :
    denoteGraphDistributedFaithful pm init 15229 =
      denoteGraphDistributedFaithful pm init 8696 :=
  denoteGraphDistributedFaithful_multiref pm init multirefCert_pm_7747_15229

#print axioms TrainVerify.Denote.denoteGraphDistributedFaithful_multiref

end TrainVerify.Denote.GeneratedPatterns
