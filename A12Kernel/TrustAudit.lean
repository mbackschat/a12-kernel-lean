import A12Kernel.Proofs

/-! Registry of every exported theorem in the trusted proof modules. The trust script
checks that this registry covers every `theorem` declaration before inspecting the
transitive axiom report below. -/

#print axioms A12Kernel.K.and_commutative
#print axioms A12Kernel.K.and_associative
#print axioms A12Kernel.K.and_idempotent
#print axioms A12Kernel.K.or_commutative
#print axioms A12Kernel.K.or_associative
#print axioms A12Kernel.K.or_idempotent
#print axioms A12Kernel.K.and_tru_left
#print axioms A12Kernel.K.and_tru_right
#print axioms A12Kernel.K.and_fls_left
#print axioms A12Kernel.K.and_fls_right
#print axioms A12Kernel.K.or_fls_left
#print axioms A12Kernel.K.or_fls_right
#print axioms A12Kernel.K.or_tru_left
#print axioms A12Kernel.K.or_tru_right
#print axioms A12Kernel.K.and_absorbs_or
#print axioms A12Kernel.K.or_absorbs_and
#print axioms A12Kernel.K.and_distributes_over_or
#print axioms A12Kernel.K.or_distributes_over_and
#print axioms A12Kernel.K.informationRefines_refl
#print axioms A12Kernel.K.definite_true_stable
#print axioms A12Kernel.K.definite_false_stable
#print axioms A12Kernel.K.and_information_monotone
#print axioms A12Kernel.K.or_information_monotone

#print axioms A12Kernel.Verdict.conj_commutative
#print axioms A12Kernel.Verdict.conj_associative
#print axioms A12Kernel.Verdict.conj_idempotent
#print axioms A12Kernel.Verdict.disj_commutative
#print axioms A12Kernel.Verdict.disj_associative
#print axioms A12Kernel.Verdict.disj_idempotent
#print axioms A12Kernel.Verdict.conj_fired_value_left
#print axioms A12Kernel.Verdict.conj_fired_value_right
#print axioms A12Kernel.Verdict.conj_notFired_left
#print axioms A12Kernel.Verdict.conj_notFired_right
#print axioms A12Kernel.Verdict.disj_notFired_left
#print axioms A12Kernel.Verdict.disj_notFired_right
#print axioms A12Kernel.Verdict.disj_fired_value_left
#print axioms A12Kernel.Verdict.disj_fired_value_right
#print axioms A12Kernel.Verdict.conj_absorbs_disj
#print axioms A12Kernel.Verdict.disj_absorbs_conj
#print axioms A12Kernel.Verdict.conj_distributes_over_disj
#print axioms A12Kernel.Verdict.disj_distributes_over_conj

#print axioms A12Kernel.formalCheck_wellFormed
#print axioms A12Kernel.withFinding_preserves_wellFormed
#print axioms A12Kernel.formalCheck_empty_observes_empty
#print axioms A12Kernel.required_empty_observes_unknown_in_validation
#print axioms A12Kernel.required_empty_observes_empty_in_computation
#print axioms A12Kernel.ordinary_finding_still_poisons_computation

#print axioms A12Kernel.desugarAbsoluteRequired_preserves
#print axioms A12Kernel.withRequiredFinding_preserves_computation
#print axioms A12Kernel.applyAbsoluteRequired_preserves_computation
#print axioms A12Kernel.requiredFinding_empty_phase_split

#print axioms A12Kernel.elaborate_success_wellFormed
#print axioms A12Kernel.elaborate_success_modelWellFormed
#print axioms A12Kernel.admitsField_has_unique_matching_declaration
#print axioms A12Kernel.checkContext_lookup_coherent
#print axioms A12Kernel.checkContext_admittedField_coherent
#print axioms A12Kernel.checkContext_lookup_error_is_malformed
#print axioms A12Kernel.checkContext_lookup_error_observes_unknown
