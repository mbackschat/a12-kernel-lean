import A12Kernel.Elaboration.BooleanConstantComputation

/-! # Boolean and Confirm constant-computation laws -/

namespace A12Kernel

/-- The checked gate accepts exactly both Boolean constants and the True-only Confirm case. -/
theorem checkBooleanConstantOperation_accepts_iff
    (targetKind : FieldKind) (value : Bool) :
    (checkBooleanConstantOperation targetKind value).isOk =
      (targetKind == .boolean || (targetKind == .confirm && value)) := by
  cases targetKind <;> cases value <;> rfl

/-- Checked constant execution returns the exact value retained by its target-kind-certified operation. -/
theorem checkedBooleanConstantComputation_execute_exact
    (operation : CheckedBooleanConstantComputation model) :
    operation.execute = .value operation.operation.operation.value := by
  rfl

/-- Constant result construction delegates source-relative classification to the shared Boolean result owner. -/
theorem checkedBooleanConstantComputation_executeResult_projects
    (operation : CheckedBooleanConstantComputation model)
    (input : CheckedDocument model) :
    (operation.executeResult input).boolean =
      BooleanComputationRunView.fromSourcedOutcomes [] [(
        operation.target.id, operation.execute,
        input.sourceBooleanTargetState operation.target.id)] := by
  rfl

/-- Checked application delegates only the retained source-relative actions to the shared Boolean destination fold. -/
theorem booleanConstantComputationRun_applyToChecked_delegates
    (view : BooleanConstantComputationRunView model)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.boolean.applyTo destination.sourceBooleanTargetState := by
  rfl

end A12Kernel
