import A12Kernel.Elaboration.StringFirstFilledComputation
import A12Kernel.Proofs.StringComputationRunApplication

/-! # Ordinary String `FirstFilledValue` laws at a fixed or a repeatable target -/

namespace A12Kernel

/-- A checked nonempty ordinary String value is the token the scan consumes. -/
theorem stringFirstFilledCell_value (field : FlatStringField) (value : String)
    (nonempty : value.isEmpty = false) :
    (FlatTextFieldOperand.string field).checkedValueListCellAt .computation {
      rawPresent := true, parsed := some (.str value), findings := []
    } = .present value := by
  have observed : observeCell .computation ({
      rawPresent := true, parsed := some (Value.str value), findings := [] } : CheckedCell) =
        .value (Value.str value) := rfl
  simp only [FlatTextFieldOperand.checkedValueListCellAt, observed, nonempty]
  rfl

/-- A reached malformed source remains poison rather than an ordinary empty String. -/
theorem stringFirstFilledCell_malformed (field : FlatStringField) (value : String) :
    (FlatTextFieldOperand.string field).checkedValueListCellAt .computation {
      rawPresent := true, parsed := some (.str value), findings := [.malformed]
    } = .unknown .malformed := by
  rfl

/-- The checked operation retains ordinary String carriers, a source that cannot read its target,
and the measured placement split: a repeatable target lies at or below its declaring group and is
no index field. -/
theorem checkedStringFirstFilled_carriersAndPlacement
    (operation : CheckedStringFirstFilledComputation model) :
    operation.target.isOrdinaryStringComputationCarrier = true ∧
      operation.source.operands.all
        (·.declarations.all (·.isOrdinaryStringComputationCarrier)) = true ∧
      operation.source.referencesField operation.targetField = false ∧
      (operation.target.repeatableScope.isEmpty ||
        (GroupPath.isPrefixOf operation.declaringGroup operation.target.groupPath &&
          !model.isIndexField operation.targetField)) = true :=
  ⟨operation.targetOrdinary, operation.sourceOrdinary, operation.excludesTarget,
    operation.targetPlaced⟩

/-- A fixed target runs exactly once, at its single instance, the empty environment. -/
theorem checkedStringFirstFilled_fixed_runsOnce
    (operation : CheckedStringFirstFilledComputation model)
    (matcher : Option (String → Bool)) (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (fixed : operation.target.repeatableScope = []) :
    operation.executeWithMatcher matcher input read =
      (·::[]) <$> operation.evaluateAt matcher input read [] := by
  simp [CheckedStringFirstFilledComputation.executeWithMatcher, fixed]

/-- The immutable executor is definitionally the caller-read route on the document's own read. -/
theorem checkedStringFirstFilled_executeWithRead_base
    (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    operation.executeWithRead patterns input input.read = operation.execute patterns input := by
  rfl

/-- Result construction retains the checked operation and classifies every outcome against its
exact immutable target state. -/
theorem checkedStringFirstFilled_executeResult_projects
    (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List StringFirstFilledComputationOutcome)
    (view : StringFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute patterns input = .ok outcomes)
    (produced : operation.executeResult patterns input messages = .ok view) :
    view.operation = operation ∧
      view.string = StringComputationRunView.fromSourcedOutcomes messages
        (outcomes.map fun entry => {
          targetField := entry.targetField
          outcome := entry.outcome
          source := input.sourceStringTargetStateAt entry.targetField }) := by
  rw [CheckedStringFirstFilledComputation.executeResult,
    CheckedStringFirstFilledComputation.executeResultWithRead] at produced
  change operation.executeWithRead patterns input input.read = .ok outcomes at executed
  rw [executed] at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- One instance's every retained action names that instance's exact target address. -/
theorem checkedStringFirstFilled_executeResult_actionsOwned
    (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (entry : StringFirstFilledComputationOutcome)
    (view : StringFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute patterns input = .ok [entry])
    (produced : operation.executeResult patterns input messages = .ok view) :
    view.string.actionTargets.all (· == entry.targetField) = true := by
  have projected := checkedStringFirstFilled_executeResult_projects operation
    patterns input messages [entry] view executed produced
  rw [projected.2]
  apply oneTargetStringResult_actionsOwned

/-- Successful whole-call composition preserves the exact prepared String result, including eager
findings, target-policy outcomes, and source-relative actions. -/
theorem checkedStringFirstFilled_executeResultWithFormalInputs_exact
    (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (result : StringFirstFilledComputationRunView model ComputationFormalInputFinding)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead patterns input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands = .ok result) :
    operation.executeResultWithFormalInputs patterns input = .ok result := by
  rw [CheckedStringFirstFilledComputation.executeResultWithFormalInputs, planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- A post-preparation execution failure retains the exact eager input findings beside the
unchanged String fault. -/
theorem checkedStringFirstFilled_executeResultWithFormalInputs_failure_exact
    (operation : CheckedStringFirstFilledComputation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (plan : CheckedComputationFormalInputPlan model)
    (prepared : ComputationFormalInputPreparation model)
    (fault : StringFirstFilledComputationFault)
    (planned : operation.formalInputPlan = .ok plan)
    (preparation : plan.prepare input = .ok prepared)
    (executed : operation.executeResultWithRead patterns input
      prepared.preliminary.readComputation prepared.formalErrorsInOperands = .error fault) :
    operation.executeResultWithFormalInputs patterns input =
      .error (.execution prepared.formalErrorsInOperands fault) := by
  rw [CheckedStringFirstFilledComputation.executeResultWithFormalInputs, planned]
  simp only [Except.mapError, bind, Except.bind, preparation, executed]

/-- Checked application delegates to the established source-classified String fold. -/
theorem stringFirstFilled_applyToChecked_delegates
    (view : StringFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
