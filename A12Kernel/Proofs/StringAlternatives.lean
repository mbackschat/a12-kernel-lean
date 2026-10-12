import A12Kernel.Proofs.ComputationCondition
import A12Kernel.Semantics.StringAlternatives

/-! # A12Kernel.Proofs.StringAlternatives — terminal selected-operation laws

These laws connect operation-neutral first-match selection and common-precondition expansion to the existing String outcome evaluator. They establish that suffix alternatives are irrelevant once a head holds, including when the selected expression later produces no value, and that a common guard decides before every alternative-specific guard. They do not assert model-level table legality, scheduling, or external kernel correspondence.
-/

namespace A12Kernel

private theorem selectFirstWith_checked (alternatives : List (ComputationAlternative Operation))
    (context : ScalarComputationContext) :
    ComputationAlternative.selectFirstWith (fun condition => condition.evalChecked context) alternatives =
      ComputationAlternative.selectFirstChecked alternatives context := rfl

/-- Clean exhaustion becomes quiet no-value at the shared String target. The converse is deliberately false because a selected expression may itself produce no value. -/
theorem stringAlternatives_noMatch_evaluates_noValue
    (computation : StringAlternativeComputation)
    (context : StringComputationContext)
    (noMatch : ComputationAlternative.selectFirstChecked computation.alternatives context =
      .ok .noMatch) :
    computation.evaluateOutcome context = .ok .noValue := by
  simp only [StringAlternativeComputation.evaluateOutcome,
    StringAlternativeComputation.evaluateOutcomeWithPattern,
    StringAlternativeComputation.evaluateOutcomeWithGuard,
    selectFirstWith_checked, noMatch, Except.mapError, bind, Except.bind]

/-- Poison reached during selection becomes target poison without evaluating an operation. -/
theorem stringAlternatives_selectionPoison_preserves
    (computation : StringAlternativeComputation)
    (context : StringComputationContext) (cause : FormalCause)
    (poisoned : ComputationAlternative.selectFirstChecked computation.alternatives context =
      .ok (.poison cause)) :
    computation.evaluateOutcome context = .ok (.poison cause) := by
  simp only [StringAlternativeComputation.evaluateOutcome,
    StringAlternativeComputation.evaluateOutcomeWithPattern,
    StringAlternativeComputation.evaluateOutcomeWithGuard,
    selectFirstWith_checked, poisoned, Except.mapError, bind, Except.bind]

/-- A selected expression delegates exactly once to the existing String step evaluator. -/
theorem stringAlternatives_selected_delegates
    (computation : StringAlternativeComputation)
    (context : StringComputationContext) (expression : StringExpr)
    (selected : ComputationAlternative.selectFirstChecked computation.alternatives context =
      .ok (.selected expression)) :
    computation.evaluateOutcome context =
      (computation.selectedStep expression).evaluateOutcome context := by
  simp only [StringAlternativeComputation.evaluateOutcome,
    StringAlternativeComputation.evaluateOutcomeWithPattern,
    StringAlternativeComputation.evaluateOutcomeWithGuard,
    selectFirstWith_checked, selected,
    StringAlternativeComputation.selectedStep,
    StringComputationStep.evaluateOutcome, Except.mapError, bind, Except.bind]
  cases expression.evaluate context with
  | error fault => rfl
  | ok store =>
      dsimp only
      cases computation.targetRegime.check computation.targetPolicy none store context <;> rfl

/-- Once the head precondition holds, its expression is evaluated and every suffix is irrelevant. -/
theorem stringAlternatives_holdingHead_evaluates
    (computation : StringAlternativeComputation)
    (context : StringComputationContext)
    (head : ComputationAlternative StringExpr)
    (remaining : List (ComputationAlternative StringExpr))
    (guard : ComputationCondition) (guarded : head.precondition = some guard)
    (holds : guard.evalChecked context = .ok .holds) :
    ({ computation with alternatives := head :: remaining }).evaluateOutcome context =
      (computation.selectedStep head.operation).evaluateOutcome context := by
  simp only [StringAlternativeComputation.evaluateOutcome,
    StringAlternativeComputation.evaluateOutcomeWithPattern,
    StringAlternativeComputation.evaluateOutcomeWithGuard,
    selectFirstWith_checked,
    ComputationAlternative.selectFirstChecked_cons, guarded, holds,
    StringAlternativeComputation.selectedStep,
    StringComputationStep.evaluateOutcome, Except.mapError, bind, Except.bind]
  cases head.operation.evaluate context with
  | error fault => rfl
  | ok store =>
      dsimp only
      cases computation.targetRegime.check computation.targetPolicy none store context <;> rfl

/-- The payoff law: two arbitrary suffixes remain observationally equal after a holding head, even though evaluating the selected expression may yield no-value, target rejection, poison, or a fragment fault. -/
theorem stringAlternatives_holdingHead_suffixIrrelevant
    (computation : StringAlternativeComputation)
    (context : StringComputationContext)
    (head : ComputationAlternative StringExpr)
    (firstSuffix secondSuffix : List (ComputationAlternative StringExpr))
    (guard : ComputationCondition) (guarded : head.precondition = some guard)
    (holds : guard.evalChecked context = .ok .holds) :
    ({ computation with alternatives := head :: firstSuffix }).evaluateOutcome context =
      ({ computation with alternatives := head :: secondSuffix }).evaluateOutcome context := by
  rw [stringAlternatives_holdingHead_evaluates computation context head firstSuffix
      guard guarded holds,
    stringAlternatives_holdingHead_evaluates computation context head secondSuffix
      guard guarded holds]

/-- A holding head whose selected expression produces no value cannot fall through to any suffix. -/
theorem stringAlternatives_selectedNoValue_doesNotFallThrough
    (computation : StringAlternativeComputation)
    (context : StringComputationContext)
    (head : ComputationAlternative StringExpr)
    (remaining : List (ComputationAlternative StringExpr))
    (guard : ComputationCondition) (guarded : head.precondition = some guard)
    (holds : guard.evalChecked context = .ok .holds)
    (noValue :
      (computation.selectedStep head.operation).evaluateOutcome context = .ok .noValue) :
    ({ computation with alternatives := head :: remaining }).evaluateOutcome context =
      .ok .noValue := by
  rw [stringAlternatives_holdingHead_evaluates computation context head remaining
      guard guarded holds, noValue]

/-- Completed target outcome is projected against the one shared prior state only after selection and operation evaluation finish. -/
theorem stringAlternatives_evaluate_of_outcome
    (computation : StringAlternativeComputation)
    (context : StringComputationContext) (outcome : StringTargetOutcome)
    (evaluated : computation.evaluateOutcome context = .ok outcome) :
    computation.evaluate context = .ok {
      outcome
      delta := outcome.projectDelta computation.prior } := by
  simp only [StringAlternativeComputation.evaluate, evaluated]

/-- A holding common precondition preserves the complete resolved String outcome because expansion leaves the first-match selection unchanged. -/
theorem stringAlternatives_holdingCommon_preserves
    (computation : StringAlternativeComputation)
    (context : StringComputationContext) (common : ComputationCondition)
    (commonHolds : common.evalChecked context = .ok .holds) :
    (computation.withCommonPrecondition (some common)).evaluateOutcome context =
      computation.evaluateOutcome context := by
  simp only [StringAlternativeComputation.evaluateOutcome,
    StringAlternativeComputation.evaluateOutcomeWithPattern,
    StringAlternativeComputation.evaluateOutcomeWithGuard,
    selectFirstWith_checked,
    StringAlternativeComputation.withCommonPrecondition]
  rw [checkedAlternativeSelection_holdingCommon_preserves context common
    computation.alternatives commonHolds]

/-- A clean non-holding common precondition produces quiet no-value for every String table, before any alternative-specific guard or operation can contribute. -/
theorem stringAlternatives_notTrueCommon_noValue
    (computation : StringAlternativeComputation)
    (context : StringComputationContext) (common : ComputationCondition)
    (commonNotTrue : common.evalChecked context = .ok .notTrue) :
    (computation.withCommonPrecondition (some common)).evaluateOutcome context =
      .ok .noValue := by
  simp only [StringAlternativeComputation.evaluateOutcome,
    StringAlternativeComputation.evaluateOutcomeWithPattern,
    StringAlternativeComputation.evaluateOutcomeWithGuard,
    selectFirstWith_checked,
    StringAlternativeComputation.withCommonPrecondition]
  rw [checkedAlternativeSelection_notTrueCommon_noMatch context common
    computation.alternatives commonNotTrue]
  rfl

/-- On a nonempty String table, common-precondition poison becomes target poison before selection can reach an otherwise-safe operation. -/
theorem stringAlternatives_poisonedCommon_preserves
    (computation : StringAlternativeComputation)
    (context : StringComputationContext) (common : ComputationCondition)
    (head : ComputationAlternative StringExpr)
    (remaining : List (ComputationAlternative StringExpr))
    (cause : FormalCause)
    (commonPoison : common.evalChecked context = .ok (.poison cause)) :
    (({ computation with alternatives := head :: remaining }).withCommonPrecondition
      (some common)).evaluateOutcome context = .ok (.poison cause) := by
  simp only [StringAlternativeComputation.evaluateOutcome,
    StringAlternativeComputation.evaluateOutcomeWithPattern,
    StringAlternativeComputation.evaluateOutcomeWithGuard,
    selectFirstWith_checked,
    StringAlternativeComputation.withCommonPrecondition]
  rw [checkedAlternativeSelection_poisonedCommon_aborts context common head remaining cause
    commonPoison]
  rfl

end A12Kernel
