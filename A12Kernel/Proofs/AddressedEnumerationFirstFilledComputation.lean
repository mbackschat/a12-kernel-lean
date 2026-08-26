import A12Kernel.Elaboration.AddressedEnumerationFirstFilledComputation
import A12Kernel.Proofs.AddressedEnumerationComputation

/-! # Repeatable Enumeration `FirstFilledValue` laws -/

namespace A12Kernel

/-- The checked target retains its nonempty repeatable scope. -/
theorem checkedAddressedEnumerationFirstFilled_target_repeatable
    (operation : CheckedAddressedEnumerationFirstFilledComputation model) :
    operation.target.declaration.repeatableScope ≠ [] :=
  operation.target.repeatable

/-- Every checked first-filled source slot is compatible with the exact target projection. -/
theorem checkedAddressedEnumerationFirstFilled_sources_allowed
    (operation : CheckedAddressedEnumerationFirstFilledComputation model) :
    ∀ operand ∈ operation.source.operands,
      operand.allowedFor operation.target.projection = true := by
  simpa [CheckedEnumerationFirstFilledSource.allowedFor] using
    operation.sourceAllowed

/-- No direct or starred source slot reads the computed target. -/
theorem checkedAddressedEnumerationFirstFilled_excludes_target_reference
    (operation : CheckedAddressedEnumerationFirstFilledComputation model) :
    operation.source.referencesField operation.target.field = false :=
  operation.targetNotReferenced

/-- Successful execution projects the exact row outcomes without changing their String result classification. -/
theorem checkedAddressedEnumerationFirstFilled_executeResult_projects
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List AddressedEnumerationComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    (operation.executeResult input residualMessages).map (fun view => view.string) =
      .ok (projectAddressedTokenResults input residualMessages outcomes) := by
  rw [CheckedAddressedEnumerationFirstFilledComputation.executeResult, executed]
  rfl

/-- Whole-domain admission leaves no runtime Enumeration target-rejection channel. -/
theorem checkedAddressedEnumerationFirstFilled_executeResult_hasNoTargetErrors
    (operation : CheckedAddressedEnumerationFirstFilledComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List AddressedEnumerationComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    (operation.executeResult input residualMessages).map
      (fun view => view.string.withErrors) = .ok [] := by
  unfold CheckedAddressedEnumerationFirstFilledComputation.executeResult
  rw [executed]
  change Except.ok
    ((projectAddressedTokenResults input residualMessages outcomes).withErrors) =
      Except.ok []
  exact congrArg Except.ok
    (addressedTokenResults_haveNoTargetErrors outcomes input residualMessages)

/-- Exact-address checked application delegates to the established source-classified String fold. -/
theorem addressedEnumerationFirstFilledRun_applyToChecked_delegates
    (view : AddressedEnumerationFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
