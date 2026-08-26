import A12Kernel.Elaboration.EnumerationFirstFilledComputation

/-! # Checked Enumeration-target `FirstFilledValue` laws -/

namespace A12Kernel

/-- Checked target compatibility covers every authored Enumeration/category source, not only the selected runtime token. -/
theorem checkedEnumerationFirstFilled_sources_allowed
    (operation : CheckedEnumerationFirstFilledComputationOperation model) :
    ∀ operand ∈ operation.source.operands,
      operand.allowedFor operation.target.projection = true := by
  simpa [CheckedEnumerationFirstFilledSource.allowedFor] using
    operation.sourceAllowed

/-- Checked Enumeration-target `FirstFilledValue` excludes its target from every direct or starred source slot. -/
theorem checkedEnumerationFirstFilled_excludes_target_reference
    (operation : CheckedEnumerationFirstFilledComputationOperation model) :
    operation.source.referencesField operation.target.field = false :=
  operation.targetNotReferenced

/-- The target wrapper delegates exactly to the common checked first-filled scan and common Enumeration target projection. -/
theorem checkedEnumerationFirstFilled_evaluate
    (operation : CheckedEnumerationFirstFilledComputationOperation model)
    (document : Document) (outer : Env) (directRead : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell) :
    operation.evaluate document outer directRead filterRead starRead = (do
      let selected ←
        operation.source.evaluate document outer directRead filterRead starRead
      pure selected.asComputationResult.asExactStringTargetOutcome) := by
  rfl

/-- Successful first-filled execution delegates its exact token result to the shared model-certified Enumeration result constructor. -/
theorem checkedEnumerationFirstFilled_executeResult_projects
    (operation : CheckedEnumerationFirstFilledComputationOperation model)
    (input : CheckedDocument model) (outer : Env)
    (directRead : RawFlatContext)
    (filterRead : Env → FieldId → CheckedCell)
    (starRead : Env → FieldId → RawCell)
    (residualMessages : List ResidualMessage)
    (selected : FirstFilledTokenResult)
    (evaluated : operation.source.evaluate input.source.toDocument outer
      directRead filterRead starRead = .ok selected) :
    operation.executeResult input outer directRead filterRead starRead
        residualMessages =
      .ok (EnumerationComputationRunView.fromTokenResult operation.target input
        residualMessages selected.asComputationResult) := by
  rw [CheckedEnumerationFirstFilledComputationOperation.executeResult, evaluated]
  rfl

end A12Kernel
