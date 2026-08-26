import A12Kernel.Elaboration.BooleanFirstFilledComputation

/-! # Direct one-star Boolean `FirstFilledValue` computation laws -/

namespace A12Kernel

/-- An exhausted Boolean source clears rather than manufacturing `false`. -/
theorem firstFilledBoolean_exhausted_noValue :
    evalFirstFilledBoolean [] = .noValue := by
  rfl

/-- `false` is a present Boolean value, not the empty-selection identity. -/
theorem firstFilledBoolean_false_is_value
    (tail : List FirstFilledBooleanCell) :
    evalFirstFilledBoolean (.present false :: tail) =
      .value false := by
  rfl

/-- Checked execution delegates the supplied outcome to the Boolean result classifier without changing its target or residual channel. -/
theorem checkedBooleanFirstFilledComputation_executeResult_projects
    (operation : CheckedBooleanFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcome : FirstFilledBooleanComputationResult)
    (evaluated : operation.execute input = .ok outcome) :
    operation.executeResult input residualMessages =
      .ok (BooleanFirstFilledComputationRunView.fromOutcome operation input
        residualMessages outcome) := by
  rw [CheckedBooleanFirstFilledComputation.executeResult, evaluated]
  rfl

end A12Kernel
