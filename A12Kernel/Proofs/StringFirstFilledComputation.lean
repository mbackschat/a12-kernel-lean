import A12Kernel.Elaboration.StringFirstFilledComputation
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Direct one-star ordinary String `FirstFilledValue` laws -/

namespace A12Kernel

/-- A checked ordinary String value remains the token consumed by first-filled selection. -/
theorem stringFirstFilledCellAt_value (value : String) :
    stringFirstFilledCellAt {
      rawPresent := true, parsed := some (.str value), findings := []
    } = .present value := by
  rfl

/-- A reached malformed source remains poison rather than an ordinary empty String. -/
theorem stringFirstFilledCellAt_malformed (value : String) :
    stringFirstFilledCellAt {
      rawPresent := true, parsed := some (.str value), findings := [.malformed]
    } = .unknown .malformed := by
  rfl

/-- Successful result construction retains the exact operation and rich target outcome. -/
theorem checkedStringFirstFilled_executeResult_projects
    (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcome : StringTargetOutcome)
    (view : StringFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute patterns input = .ok outcome)
    (produced : operation.executeResult patterns input messages = .ok view) :
    view.operation = operation ∧
      view.string = StringComputationRunView.fromSourcedOutcomes messages [{
        targetField := operation.target.id
        outcome
        source := input.sourceStringTargetState operation.target.id
      }] := by
  rw [CheckedStringFirstFilledComputation.executeResult, executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Every retained action names the checked ordinary String target. -/
theorem checkedStringFirstFilled_executeResult_actionsOwned
    (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcome : StringTargetOutcome)
    (view : StringFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute patterns input = .ok outcome)
    (produced : operation.executeResult patterns input messages = .ok view) :
    view.string.actionTargets.all (· == operation.target.id) = true := by
  have projected := checkedStringFirstFilled_executeResult_projects operation
    patterns input messages outcome view executed produced
  rw [projected.2]
  apply oneTargetStringResult_actionsOwned

/-- Same-model application delegates to the established source-classified String fold. -/
theorem stringFirstFilled_applyToChecked_delegates
    (view : StringFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetState := by
  rfl

end A12Kernel
