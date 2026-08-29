import A12Kernel.Elaboration.AddressedNumberFirstFilledGeneratedValidation

/-! # Exact-address repeatable Number `FirstFilledValue` laws -/

namespace A12Kernel

/-- The checked operation retains one model-owned Number target and a nonempty authored list whose every operand is a model-owned Number star with bounded sibling placement and exact source/target scale. -/
theorem checkedAddressedNumberFirstFilled_sound
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    model.validate.isOk = true ∧
      model.lookupUniqueId operation.targetField =
        .ok operation.targetDeclaration ∧
      GroupPath.isPrefixOf operation.declaringGroup
        operation.targetDeclaration.groupPath = true ∧
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
    operation.target.targetContainedInDeclaringGroup, operation.target.targetPolicyOwned,
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

/-- The immutable addressed executor is exactly the caller-read executor specialized to the checked document's own read. -/
theorem checkedAddressedNumberFirstFilled_executeWithRead_base
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (input : CheckedDocument model) :
    operation.executeWithRead input input.read = operation.execute input := by
  rfl

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
  rw [CheckedAddressedNumberFirstFilledComputation.executeResult,
    CheckedAddressedNumberFirstFilledComputation.executeResultWithRead]
    at produced
  change operation.executeWithRead input input.read = .ok outcomes at executed
  rw [executed] at produced
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

/-- The generated repeatable mismatch keeps the computed target on its left, the complete checked first-filled source on its right, and no caller-selectable scale-warning suppression. -/
theorem addressedNumberFirstFilled_generatedMismatch_exact
    (operation : CheckedAddressedNumberFirstFilledComputation model) :
    let comparison := operation.generatedMismatchComparison
    comparison.op = .ordinary .notEqual ∧
      comparison.left =
        .atom (.ordinary (.field operation.generatedValidationTarget)) ∧
      comparison.right = .atom (.firstFilled operation.numberSource) ∧
      comparison.suppressExactScaleWarning = false := by
  simp [CheckedAddressedNumberFirstFilledComputation.generatedMismatchComparison]

/-- The materialized continuation is deliberately two-level only and refuses a deeper checked target before any runtime phase. -/
theorem addressedNumberFirstFilled_materializedValidation_rejectsThreeLevels
    (operation : CheckedAddressedNumberFirstFilledComputation model)
    (source destination : CheckedDocument model)
    (payloadAt : CellAddr → Payload)
    (supplied : List (ComputationFormalMessage Payload))
    (errorCode : String) (messagePlan : MessageRenderPlan)
    (outer middle inner : RepeatableLevel)
    (scope : operation.targetDeclaration.repeatableScope =
      [outer, middle, inner]) :
    operation.executeGeneratedMaterializedAppliedValidation source destination
      payloadAt supplied errorCode messagePlan =
        .error (.targetScope [outer, middle, inner]) := by
  simp [CheckedAddressedNumberFirstFilledComputation.executeGeneratedMaterializedAppliedValidation,
    scope] <;> rfl

end A12Kernel
