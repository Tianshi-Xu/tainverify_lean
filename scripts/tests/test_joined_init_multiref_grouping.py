from __future__ import annotations

import unittest
from dataclasses import replace
from types import SimpleNamespace

from trainverify.bridge_emitter.relation_compiler import (
    CertificateTransitionSpec,
    JoinedInitMultirefCertificate,
    JoinedInitMultirefGroupCertificate,
    RelationCompositionError,
    RelationFactSpec,
    TransitionAuthorityRequirement,
    build_atomic_schedule,
    group_joined_init_multiref_certificates,
)


class JoinedInitMultirefGroupingTests(unittest.TestCase):
    def certificate(self, projection: int) -> JoinedInitMultirefCertificate:
        source = RelationFactSpec("joined", ("init:7",), joined_pm_step="init:7")
        output = RelationFactSpec(
            "joined", ("init:7",), joined_pm_step=f"pm:11:{projection}"
        )
        return JoinedInitMultirefCertificate(
            rule_id="joined-init-multiref-alias",
            input_fact=source,
            output_fact=output,
            pm_step_id=f"pm:11:{projection}",
            projection=projection,
            arity=3,
            lean_theorem="TrainVerify.Denote.applyNode_fw_multiref_at",
        )

    def test_two_outputs_share_one_writer_transition(self):
        grouped = group_joined_init_multiref_certificates(
            (self.certificate(1), self.certificate(0))
        )
        self.assertEqual(len(grouped), 1)
        item = grouped[0]
        self.assertIs(type(item), JoinedInitMultirefGroupCertificate)
        self.assertEqual(item.projections, (0, 1))
        self.assertEqual(item.pm_step_ids, ("pm:11:0", "pm:11:1"))
        self.assertEqual(
            tuple(fact.joined_pm_step for fact in item.output_facts),
            ("pm:11:0", "pm:11:1"),
        )

    def test_duplicate_projection_fails_closed(self):
        with self.assertRaisesRegex(RelationCompositionError, "duplicate projection"):
            group_joined_init_multiref_certificates(
                (self.certificate(0), self.certificate(0))
            )

    def test_malformed_projection_authority_fails_closed(self):
        with self.assertRaisesRegex(RelationCompositionError, "out of range"):
            group_joined_init_multiref_certificates(
                (replace(self.certificate(0), projection=3),)
            )
        with self.assertRaisesRegex(RelationCompositionError, "projection/fact identity"):
            group_joined_init_multiref_certificates(
                (replace(self.certificate(0), pm_step_id="pm:11:1"),)
            )

    def test_fact_only_adapter_attaches_to_exact_producer_without_owning_node(self):
        ordinary = RelationFactSpec("ordinary", ("sm:0:0", "pm:0:0", "pm:1:0"))
        sharded = RelationFactSpec(
            "sharded", ordinary.step_triple, gather_dim=0
        )
        producer = CertificateTransitionSpec(
            transition_id="producer", rule_id="producer", pre_facts=(),
            post_facts=(ordinary,), sm_node_indices=(0,), pm_node_indices=(0, 1),
            lean_theorem="Producer.theorem",
        )
        adapter = CertificateTransitionSpec(
            transition_id="adapter", rule_id="adapter", pre_facts=(ordinary,),
            post_facts=(sharded,), sm_node_indices=(), pm_node_indices=(),
            lean_theorem="Adapter.theorem", fact_only=True,
        )
        node = lambda rank, output: SimpleNamespace(
            rank=rank, op="FW_view", ins=[output - 1], outs=[output], params=[]
        )
        ir = SimpleNamespace(sm_nodes=[node(0, 1)], pm_nodes=[node(0, 2), node(1, 3)])
        plan = build_atomic_schedule(ir, (producer, adapter))
        self.assertEqual(plan.transition_components["producer"], plan.transition_components["adapter"])
        self.assertEqual(len(plan.components), 1)

    def test_transition_digest_binds_certificate_and_authority_payloads(self):
        fact = RelationFactSpec("joined", ("init:1",), joined_pm_step="init:1")
        node = SimpleNamespace(rank=0, op="FW_view", ins=[1], outs=[2], params=[])
        ir = SimpleNamespace(sm_nodes=[node], pm_nodes=[])
        requirement = TransitionAuthorityRequirement(
            kind="tensor_shape", sides=("sm",), tids=(1,), shape=(4,)
        )
        transition = CertificateTransitionSpec(
            transition_id="producer", rule_id="producer", pre_facts=(),
            post_facts=(fact,), sm_node_indices=(0,), pm_node_indices=(),
            lean_theorem="Producer.theorem", certificate_digest="a" * 64,
            authority_requirements=(requirement,),
        )
        baseline = build_atomic_schedule(ir, (transition,)).transition_digest
        changed_certificate = build_atomic_schedule(
            ir, (replace(transition, certificate_digest="b" * 64),)
        ).transition_digest
        changed_authority = build_atomic_schedule(
            ir, (replace(transition, authority_requirements=(replace(requirement, shape=(5,)),)),)
        ).transition_digest
        self.assertNotEqual(baseline, changed_certificate)
        self.assertNotEqual(baseline, changed_authority)

    def test_fact_only_footprint_contract_fails_closed(self):
        fact = RelationFactSpec("joined", ("init:1",), joined_pm_step="init:1")
        ir = SimpleNamespace(sm_nodes=[], pm_nodes=[])
        empty_owner = CertificateTransitionSpec(
            transition_id="bad", rule_id="bad", pre_facts=(), post_facts=(fact,),
            sm_node_indices=(), pm_node_indices=(), lean_theorem="Bad.theorem",
        )
        with self.assertRaisesRegex(RelationCompositionError, "empty footprint"):
            build_atomic_schedule(ir, (empty_owner,), external_pre_facts=frozenset())


if __name__ == "__main__":
    unittest.main()
