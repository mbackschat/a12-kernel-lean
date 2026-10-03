import A12Kernel.Elaboration.StringComputationTable
import A12Kernel.Proofs.StringAlternatives

/-! # Checked String-computation table laws

These laws expose the certificate and erasure boundary used by the later checked run. They make no scheduling, result-projection, application, or external-correspondence claim.
-/

namespace A12Kernel

/-- Every present checked-row guard is a model-admitted condition. -/
theorem checkedStringComputationAlternative_guard_wellFormed
    (alternative : CheckedStringComputationAlternative model target) :
    alternative.precondition.all (·.wellFormedBool) = true :=
  alternative.guardWellFormed

/-- Every present checked-row guard excludes its own target before evaluation. -/
theorem checkedStringComputationAlternative_excludes_target
    (alternative : CheckedStringComputationAlternative model target) :
    alternative.precondition.all
      (fun guard => !guard.forbidsTarget target) = true :=
  alternative.guardExcludesTarget

/-- Every checked row also retains operation-side target exclusion after target consolidation. -/
theorem checkedStringComputationAlternative_expression_excludes_target
    (alternative : CheckedStringComputationAlternative model target) : alternative.expression.core.referencesField target = false :=
  alternative.expressionExcludesTarget

/-- Table evaluation erases certificates and projects a reached guard value failure to invalid no-value (spec/09 §3.2), without rebuilding selection. -/
theorem checkedStringComputationTable_evaluateOutcome_erases
    (table : CheckedStringComputationTable model)
    (wholeValueMatches? : Option (String → Bool)) (context : StringComputationContext) (guardContext : ScalarComputationContext) :
    table.evaluateOutcomeWithPattern wholeValueMatches? context guardContext =
      (match (table.toResolved .empty).evaluateOutcomeWithGuard
          (fun condition => condition.evalChecked guardContext)
          CheckedStringComputationFault.guard CheckedStringComputationFault.operation wholeValueMatches? context with
        | .error (.guard (.predicate .valueFailure)) => .ok .invalidNoValue
        | result => result) := by
  rfl

end A12Kernel
