import A12Kernel.Elaboration.StringComputationTable
import A12Kernel.Proofs.StringAlternatives

/-! # Checked String-computation table laws

These laws expose the certificate and erasure boundary used by the later checked run. They make no scheduling, result-projection, application, or external-correspondence claim.
-/

namespace A12Kernel

/-- Every checked row retains a model-admitted direct-presence guard. -/
theorem checkedStringComputationAlternative_guard_wellFormed
    (alternative : CheckedStringComputationAlternative model target) : alternative.precondition.WellFormed model :=
  alternative.guardWellFormed

/-- Every checked row excludes its own target from the guard before evaluation. -/
theorem checkedStringComputationAlternative_excludes_target
    (alternative : CheckedStringComputationAlternative model target) : alternative.precondition.referencesField target = false :=
  alternative.guardExcludesTarget

/-- Every checked row also retains operation-side target exclusion after target consolidation. -/
theorem checkedStringComputationAlternative_expression_excludes_target
    (alternative : CheckedStringComputationAlternative model target) : alternative.expression.core.referencesField target = false :=
  alternative.expressionExcludesTarget

/-- Table evaluation erases certificates and delegates to the established resolved first-match evaluator without rebuilding selection. -/
theorem checkedStringComputationTable_evaluateOutcome_erases
    (table : CheckedStringComputationTable model)
    (wholeValueMatches? : Option (String → Bool)) (context : StringComputationContext) :
    table.evaluateOutcomeWithPattern wholeValueMatches? context =
      (table.toResolved .empty).evaluateOutcomeWithPattern wholeValueMatches? context := by
  rfl

end A12Kernel
