import A12Kernel.Elaboration.AddressedCustomFirstFilledComputation
import A12Kernel.Proofs.ExactTokenComputationResult

/-! # Exact-address repeatable Custom `FirstFilledValue` laws -/

namespace A12Kernel

/-- The checked source carries the target's Custom declaration and has one reopened star axis with a nonempty outer prefix supplied by the target scope. -/
theorem checkedAddressedCustomFirstFilled_source_bounded
    (operation : CheckedAddressedCustomFirstFilledComputation model) :
    operation.target.customType = some operation.customType ∧
      operation.source.declaration.customType = some operation.customType ∧
      operation.source.reopenedScope.length = 1 ∧
      operation.source.bindingScope ≠ [] ∧
      operation.source.bindingScope.all
        operation.target.repeatableScope.contains = true :=
  ⟨operation.targetCustom, operation.sourceCustom,
    operation.sourceSingleReopenedAxis, operation.sourceBindingNonempty,
    operation.sourceBindingBound⟩

/-- Addressed result construction retains the checked operation and classifies every outcome against its exact immutable target state. -/
theorem checkedAddressedCustomFirstFilled_executeResult_projects
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedCustomFirstFilledComputationOutcome)
    (view : AddressedCustomFirstFilledComputationRunView model ResidualMessage)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input messages = .ok view) :
    view.operation = operation ∧
      view.string = projectAddressedTokenResults input messages outcomes := by
  rw [CheckedAddressedCustomFirstFilledComputation.executeResult, executed]
    at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Exact-token Custom selection cannot create an ordinary String target-rejection channel. -/
theorem checkedAddressedCustomFirstFilled_executeResult_hasNoTargetErrors
    (operation : CheckedAddressedCustomFirstFilledComputation model)
    (input : CheckedDocument model) (messages : List ResidualMessage)
    (outcomes : List AddressedCustomFirstFilledComputationOutcome)
    (executed : operation.execute input = .ok outcomes) :
    (operation.executeResult input messages).map
      (fun view => view.string.withErrors) = .ok [] := by
  unfold CheckedAddressedCustomFirstFilledComputation.executeResult
  rw [executed]
  change Except.ok
    ((projectAddressedTokenResults input messages outcomes).withErrors) =
      Except.ok []
  exact congrArg Except.ok
    (addressedTokenResults_haveNoTargetErrors outcomes input messages)

/-- Exact-address checked application delegates to the established source-classified String fold. -/
theorem addressedCustomFirstFilledRun_applyToChecked_delegates
    (view : AddressedCustomFirstFilledComputationRunView model ResidualMessage)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.string.applyTo destination.sourceStringTargetStateAt := by
  rfl

end A12Kernel
