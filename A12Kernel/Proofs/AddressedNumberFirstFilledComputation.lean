import A12Kernel.Elaboration.AddressedNumberFirstFilledComputation

/-! # Exact-address repeatable Number `FirstFilledValue` laws -/

namespace A12Kernel

/-- The checked operation retains one model-owned Number target and a nonempty authored list whose every operand is a model-owned Number star with bounded sibling placement and exact source/target scale. -/
theorem checkedAddressedNumberFirstFilled_sound
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    model.validate.isOk = true ∧
      model.lookupUniqueId operation.targetField =
        .ok operation.targetDeclaration ∧
      operation.targetDeclaration.groupPath = operation.declaringGroup ∧
      operation.targetDeclaration.toNumericTargetPolicy? =
        some operation.target.targetPolicy ∧
      operation.operands ≠ [] ∧
      ∀ operand ∈ operation.operands,
        operand.source.source.declaration.toNumberField? =
          some operand.source.field ∧
        operand.source.source.reopenedScope.length = 1 ∧
        operand.source.source.bindingScope ≠ [] ∧
        operand.source.source.bindingScope.isPrefixOf
          operation.targetDeclaration.repeatableScope = true ∧
        operand.source.source.bindingScope ≠
          operation.targetDeclaration.repeatableScope ∧
        operand.source.source.reopenedScope.all (fun level =>
          !operation.targetDeclaration.repeatableScope.contains level) = true ∧
        operand.source.source.bindingScope.all
          operation.targetDeclaration.repeatableScope.contains = true ∧
        operand.source.source.declaration.id ≠ operation.targetField ∧
        exactNumericScaleComparisonAllowedWithSuppression false
          (NumericScaleSummary.field operation.target.targetPolicy.info.scale)
          (NumericScaleSummary.field operand.source.field.info.scale) = true := by
  refine ⟨operation.target.modelWellFormed, operation.target.targetOwned,
    operation.target.targetInDeclaringGroup, operation.target.targetPolicyOwned,
    ?_, ?_⟩
  · simp [CheckedAddressedNumberFirstFilledComputation.operands]
  · intro operand _
    exact ⟨operand.source.fieldOwned,
      operand.placement.sourceSingleReopenedAxis,
      operand.placement.sourceBindingNonempty,
      operand.placement.sourceBindingPrefix,
      operand.placement.sourceBindingStrict,
      operand.placement.sourceReopenedOutsideTarget,
      operand.placement.sourceBindingBound,
      operand.placement.targetNotReferenced,
      operand.targetAdmitted⟩

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
