import A12Kernel.Elaboration.AddressedNumberFirstFilledComputation

/-! # Exact-address repeatable Number `FirstFilledValue` laws -/

namespace A12Kernel

/-- The checked operation retains one model-owned Number target, one model-owned Number star, the bounded sibling placement, and exact source/target scale. -/
theorem checkedAddressedNumberFirstFilled_sound
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    model.validate.isOk = true ∧
      model.lookupUniqueId operation.targetField =
        .ok operation.targetDeclaration ∧
      operation.source.source.declaration.toNumberField? =
        some operation.source.field ∧
      operation.source.source.reopenedScope.length = 1 ∧
      operation.source.source.bindingScope ≠ [] ∧
      operation.source.source.bindingScope.isPrefixOf
        operation.targetDeclaration.repeatableScope = true ∧
      operation.source.source.bindingScope ≠
        operation.targetDeclaration.repeatableScope ∧
      operation.source.source.reopenedScope.all (fun level =>
        !operation.targetDeclaration.repeatableScope.contains level) = true ∧
      operation.source.source.bindingScope.all
        operation.targetDeclaration.repeatableScope.contains = true ∧
      operation.source.source.declaration.id ≠ operation.targetField ∧
      exactNumericScaleComparisonAllowedWithSuppression false
        (NumericScaleSummary.field operation.target.targetPolicy.info.scale)
        (NumericScaleSummary.field operation.source.field.info.scale) = true := by
  exact ⟨operation.target.modelWellFormed, operation.placement.targetOwned,
    operation.source.fieldOwned, operation.sourceSingleReopenedAxis,
    operation.sourceBindingNonempty, operation.placement.sourceBindingPrefix,
    operation.placement.sourceBindingStrict,
    operation.placement.sourceReopenedOutsideTarget,
    operation.sourceBindingBound,
    operation.targetNotReferenced, operation.targetAdmitted⟩

/-- Addressed result construction retains the checked operation and delegates every source-relative public partition to the shared exact Number result owner. -/
theorem checkedAddressedNumberFirstFilled_executeResult_projects
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (input : CheckedDocument model) (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload))
    (outcomes : List (SourcedNumericTargetOutcome CellAddr))
    (view : AddressedNumberFirstFilledComputationRunView model Payload)
    (executed : operation.execute input = .ok outcomes)
    (produced : operation.executeResult input payloadAt supplied = .ok view) :
    view.operation = operation ∧
      view.numeric = NumericComputationRunView.fromSourceOutcomesWithMessages
        MessagePointer.ofCellAddr payloadAt supplied outcomes := by
  rw [CheckedAddressedNumberFirstFilledComputation.executeResult, executed]
    at produced
  simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at produced
  subst view
  exact ⟨rfl, rfl⟩

/-- Addressed application is exactly the common Number fold over a separately supplied checked destination. -/
theorem addressedNumberFirstFilledRun_applyToChecked_delegates
    (view : AddressedNumberFirstFilledComputationRunView model Payload)
    (destination : CheckedDocument model) :
    view.applyToChecked destination =
      view.numeric.applyToChecked destination := by
  rfl

end A12Kernel
