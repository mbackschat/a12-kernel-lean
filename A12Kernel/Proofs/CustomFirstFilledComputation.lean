import A12Kernel.Elaboration.CustomFirstFilledComputation
import A12Kernel.Proofs.ExactTokenComputationResult
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Direct one-star Custom `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- A clean prepared Custom String remains the exact token consumed by the shared first-filled scan. -/
theorem customFirstFilledCellAt_value (value : String) :
    customFirstFilledCellAt {
      rawPresent := true, parsed := some (.str value), findings := []
    } = .present value := by
  rfl

/-- A registered Custom rejection retains its exact cause at the computation adapter. -/
theorem customFirstFilledCellAt_registeredRejection
    (value : String) (rejection : RegisteredCustomRejection) :
    customFirstFilledCellAt {
      rawPresent := true
      parsed := some (.str value)
      findings := [.registeredCustomValidation rejection]
    } = .unknown (.registeredCustomValidation rejection) := by
  rfl

/-- Successful result construction retains the exact checked Custom operation rather than a separately forgeable target key. -/
theorem checkedCustomFirstFilledComputation_executeResult_operation
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (completed : operation.executeResult input residualMessages = .ok view) :
    view.operation = operation := by
  cases executed : operation.execute input with
  | error cause =>
      simp [CheckedCustomFirstFilledComputation.executeResult, executed,
        Functor.map, Except.map] at completed
  | ok result =>
      simp [CheckedCustomFirstFilledComputation.executeResult, executed,
        Functor.map, Except.map] at completed
      subst view
      rfl

/-- A successful checked Custom result cannot enter the ordinary String target-rejection channel. -/
theorem checkedCustomFirstFilledComputation_executeResult_hasNoTargetErrors
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (completed : operation.executeResult input residualMessages = .ok view) :
    view.string.withErrors = [] := by
  cases executed : operation.execute input with
  | error cause =>
      simp [CheckedCustomFirstFilledComputation.executeResult, executed,
        Functor.map, Except.map] at completed
  | ok result =>
      simp [CheckedCustomFirstFilledComputation.executeResult, executed,
        Functor.map, Except.map] at completed
      subst view
      apply exactTokenStringResult_hasNoTargetErrors

/-- Every retained action from checked Custom result construction names its exact admitted target. -/
theorem checkedCustomFirstFilledComputation_executeResult_actionsOwned
    (operation : CheckedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (completed : operation.executeResult input residualMessages = .ok view) :
    view.string.actionTargets.all (· == operation.target.id) = true := by
  cases executed : operation.execute input with
  | error cause =>
      simp [CheckedCustomFirstFilledComputation.executeResult, executed,
        Functor.map, Except.map] at completed
  | ok result =>
      simp [CheckedCustomFirstFilledComputation.executeResult, executed,
        Functor.map, Except.map] at completed
      subst view
      apply oneTargetStringResult_actionsOwned

/-- Model-indexed checked Custom application delegates exactly to the established source-classified String fold over the separately supplied destination. -/
theorem customFirstFilledComputationRun_applyToChecked_delegates
    (view : CustomFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetState := by
  rfl

end A12Kernel
