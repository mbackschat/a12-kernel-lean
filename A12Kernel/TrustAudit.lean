import A12Kernel
import A12Kernel.Trust.Environment

/-!
The elaborated-environment audit is authoritative: it checks every declaration in the
trusted project modules regardless of source modifiers, attributes, or command macros.
Conformance modules are deliberately outside this root because their executable locks
may use `native_decide`. The explicit theorem reports below remain the human-readable
proof-spine registry.
-/

open Lean Lean.Elab Command

private def isAuditedProjectModule (moduleName : Name) : Bool :=
  let text := moduleName.toString
  let isProject := text == "A12Kernel" || text.startsWith "A12Kernel."
  let isConformance := text == "A12Kernel.Conformance" || text.startsWith "A12Kernel.Conformance."
  let isTrustDriver := text == "A12Kernel.Trust" || text.startsWith "A12Kernel.Trust."
  isProject && !isConformance && !isTrustDriver

run_cmd do
  let (moduleCount, declarationCount) ←
    A12Kernel.Trust.auditImportedModules isAuditedProjectModule
  logInfo m!"environment trust audit passed: {declarationCount} declarations in {moduleCount} modules"

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

#print axioms A12Kernel.selectRows_iff
#print axioms A12Kernel.sumSelected_filter_before_consumer
#print axioms A12Kernel.outer_number_reference_stable
#print axioms A12Kernel.inner_number_reference_local
#print axioms A12Kernel.correlatedHaving_truth_iff_holds
#print axioms A12Kernel.selectCorrelatedRows_iff
#print axioms A12Kernel.evalGuardedAnyFilledOn_filter_before_consumer
#print axioms A12Kernel.currentRepetition_selfExclusion_false
#print axioms A12Kernel.explicitSelfExclusion_drops_outer
#print axioms A12Kernel.sameFieldEquality_selfMatches

#print axioms A12Kernel.checkedSingleCorrelatedRule_wellFormed
#print axioms A12Kernel.checkedSingleCorrelatedRule_modelWellFormed
#print axioms A12Kernel.rawSingleGroupContext_validate_wellFormed
#print axioms A12Kernel.admitsSingleGroupNumber_has_unique_matching_declaration
#print axioms A12Kernel.checkSingleGroupContext_lookup_coherent
#print axioms A12Kernel.checkSingleGroupContext_lookup_error_is_malformed
#print axioms A12Kernel.checkSingleGroupContext_wrong_group_is_malformed
#print axioms A12Kernel.checkSingleGroupContext_wrong_scope_is_malformed
#print axioms A12Kernel.checkSingleGroupContext_admittedNumber_coherent
#print axioms A12Kernel.correlatedHaving_wellFormed_equalityScalesAgree
#print axioms A12Kernel.resolvedSingleCorrelatedRule_wellFormed_equalityScalesAgree

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
#print axioms A12Kernel.formalCheck_parsedEmptyString_observes_empty
#print axioms A12Kernel.required_empty_observes_unknown_in_validation
#print axioms A12Kernel.required_empty_observes_empty_in_computation
#print axioms A12Kernel.ordinary_finding_still_poisons_computation

#print axioms A12Kernel.desugarAbsoluteRequired_preserves
#print axioms A12Kernel.withRequiredFinding_preserves_computation
#print axioms A12Kernel.applyAbsoluteRequired_preserves_computation
#print axioms A12Kernel.requiredFinding_empty_phase_split

#print axioms A12Kernel.checkedFlatCondition_wellFormed
#print axioms A12Kernel.checkedFlatCondition_modelWellFormed
#print axioms A12Kernel.admitsField_has_unique_matching_declaration
#print axioms A12Kernel.admitsComparison_has_unique_matching_declaration
#print axioms A12Kernel.checkContext_lookup_coherent
#print axioms A12Kernel.checkContext_admittedField_coherent
#print axioms A12Kernel.checkContext_admittedComparison_coherent
#print axioms A12Kernel.checkContext_lookup_error_is_malformed
#print axioms A12Kernel.checkContext_lookup_error_observes_unknown

#print axioms A12Kernel.fixedNumericFiring_is_value
#print axioms A12Kernel.growOnlyGreaterEqualFiring_is_value
#print axioms A12Kernel.growOnlyLessFiring_is_omission
#print axioms A12Kernel.growOnlyNotEqualWhenLeftNotBelow_is_value

#print axioms A12Kernel.directEmptyStringComparison_notFired
#print axioms A12Kernel.emptyStringLengthLess_fires_omission
#print axioms A12Kernel.emptyStringLengthGreaterEqual_fires_value
#print axioms A12Kernel.emptyString_operatorDistinction
