import A12Kernel.Elaboration.EnumerationComputationResult
import A12Kernel.Proofs.ExactTokenComputationResult
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Ordinary Enumeration computation result and application laws -/

namespace A12Kernel

/-- Result construction retains the exact model-certified Enumeration target. -/
theorem checkedEnumerationComputation_executeResult_target
    (operation : CheckedEnumerationComputationOperation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    (operation.executeResult input residualMessages).target = operation.target := by
  rfl

/-- Static Enumeration-domain compatibility makes a runtime target-rejection channel impossible; exact values, no-value, and source poison still use the other shared String-shaped channels. -/
theorem checkedEnumerationComputation_executeResult_hasNoTargetErrors
    (operation : CheckedEnumerationComputationOperation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    (operation.executeResult input residualMessages).string.withErrors = [] := by
  apply exactTokenStringResult_hasNoTargetErrors

/-- Every retained action from ordinary Enumeration result construction names its exact certified target. -/
theorem checkedEnumerationComputation_executeResult_actionsOwned
    (operation : CheckedEnumerationComputationOperation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    (operation.executeResult input residualMessages).string.actionTargets.all
      (· == operation.target.field) = true := by
  apply oneTargetStringResult_actionsOwned

/-- Model-indexed checked Enumeration application delegates exactly to the established source-classified String fold over the separately supplied destination. -/
theorem enumerationComputationRun_applyToChecked_delegates
    (view : EnumerationComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetState := by
  rfl

end A12Kernel
