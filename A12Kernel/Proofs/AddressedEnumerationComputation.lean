import A12Kernel.Elaboration.AddressedEnumerationComputation
import A12Kernel.Proofs.ExactTokenComputationResult

/-! # Repeatable Enumeration computation laws -/

namespace A12Kernel

/-- The checked operation retains the target's nonempty repeatable scope. -/
theorem checkedAddressedEnumeration_target_repeatable
    (operation : CheckedAddressedEnumerationComputation model) :
    operation.target.declaration.repeatableScope ≠ [] :=
  operation.target.repeatable

/-- Every checked source has passed complete target-domain compatibility. -/
theorem checkedAddressedEnumeration_source_allowed
    (operation : CheckedAddressedEnumerationComputation model) :
    operation.source.allowedFor operation.target.projection = true :=
  operation.sourceAllowed

/-- The checked source cannot read its own computed target. -/
theorem checkedAddressedEnumeration_excludes_target_reference
    (operation : CheckedAddressedEnumerationComputation model) :
    operation.source.referencesField operation.target.field = false :=
  operation.targetNotReferenced

theorem addressedEnumerationResults_haveNoTargetErrors
    (outcomes : List AddressedEnumerationComputationOutcome)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    (projectAddressedEnumerationResults input residualMessages outcomes).withErrors =
      [] := by
  exact addressedTokenResults_haveNoTargetErrors outcomes input residualMessages

/-- Successful addressed execution cannot create the ordinary String target-rejection channel because the checked Enumeration domain gate precedes runtime. -/
theorem checkedAddressedEnumeration_executeResult_hasNoTargetErrors
    (operation : CheckedAddressedEnumerationComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage)
    (outcomes : List AddressedEnumerationComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    (operation.executeResult input residualMessages).map
      (fun view => view.string.withErrors) = .ok [] := by
  unfold CheckedAddressedEnumerationComputation.execute at executed
  unfold CheckedAddressedEnumerationComputation.executeResult
  unfold CheckedAddressedEnumerationComputation.executeResultWithRead
  rw [executed]
  change Except.ok
    ((projectAddressedEnumerationResults input residualMessages outcomes).withErrors) =
      Except.ok []
  exact congrArg Except.ok
    (addressedEnumerationResults_haveNoTargetErrors outcomes input residualMessages)

/-- Exact-address checked application delegates to the established source-classified String fold. -/
theorem addressedEnumerationRun_applyToChecked_delegates
    (view : AddressedEnumerationComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
