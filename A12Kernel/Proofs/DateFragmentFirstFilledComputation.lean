import A12Kernel.Elaboration.DateFragmentFirstFilledComputation
import A12Kernel.Proofs.ExactTokenComputationResult
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Direct one-star DateFragment `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- A clean checked DateFragment value retains the token presented to the bounded first-filled adapter. -/
theorem dateFragmentFirstFilledCellAt_value
    (addressed : CheckedAddressedCell) (date : DateValue) (token : String)
    (observed : observeCell .computation addressed.cell =
      .value (.temporal (.date date)))
    (stored : addressed.stored = some token) :
    dateFragmentFirstFilledCellAt addressed = .present token := by
  simp [dateFragmentFirstFilledCellAt, observed, stored]

/-- A reached formal rejection retains its exact cause at the DateFragment computation adapter. -/
theorem dateFragmentFirstFilledCellAt_poison
    (addressed : CheckedAddressedCell) (cause : FormalCause)
    (observed : observeCell .computation addressed.cell = .poison cause) :
    dateFragmentFirstFilledCellAt addressed = .unknown cause := by
  simp [dateFragmentFirstFilledCellAt, observed]

/-- Successful result construction retains the exact checked DateFragment operation. -/
theorem checkedDateFragmentFirstFilled_executeResult_operation
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (selected : TokenComputationResult)
    (executed : operation.execute input = .ok selected)
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (produced : operation.executeResult input residualMessages = .ok view) :
    view.operation = operation := by
  rw [CheckedDateFragmentFirstFilledComputation.executeResult, executed] at produced
  cases produced
  rfl

/-- Exact-token DateFragment result construction cannot create a target-rejection channel. -/
theorem checkedDateFragmentFirstFilled_executeResult_hasNoTargetErrors
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (selected : TokenComputationResult)
    (executed : operation.execute input = .ok selected)
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (produced : operation.executeResult input residualMessages = .ok view) :
    view.string.withErrors = [] := by
  rw [CheckedDateFragmentFirstFilledComputation.executeResult, executed] at produced
  cases produced
  apply exactTokenStringResult_hasNoTargetErrors

/-- Every retained DateFragment action names the checked operation's exact target. -/
theorem checkedDateFragmentFirstFilled_executeResult_actionsOwned
    (operation : CheckedDateFragmentFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (selected : TokenComputationResult)
    (executed : operation.execute input = .ok selected)
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (produced : operation.executeResult input residualMessages = .ok view) :
    view.string.actionTargets.all (· == operation.targetField) = true := by
  rw [CheckedDateFragmentFirstFilledComputation.executeResult, executed] at produced
  cases produced
  apply oneTargetStringResult_actionsOwned

/-- Same-model DateFragment application delegates exactly to the established source-classified text fold over the separately supplied destination. -/
theorem dateFragmentFirstFilled_applyToChecked_delegates
    (view : DateFragmentFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetState := by
  rfl

end A12Kernel
