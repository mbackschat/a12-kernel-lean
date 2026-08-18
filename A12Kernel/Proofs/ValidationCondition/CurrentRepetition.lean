import A12Kernel.Proofs.ValidationCondition
import A12Kernel.Proofs.NumericComparison
import A12Kernel.Proofs.Verdict

/-! # Checked CurrentRepetition laws -/

namespace A12Kernel

/-- The closed comparison tag delegates to the shared fixed numeric comparison and therefore preserves VALUE polarity for the one firing branch. -/
@[simp]
theorem rootCurrentRepetitionComparison_results :
    RootCurrentRepetitionComparison.equalOne.eval = .fired .value ∧
      RootCurrentRepetitionComparison.notEqualOne.eval = .notFired := by
  constructor
  · apply fixedNumericFiring_is_value
    simp [RootCurrentRepetitionComparison.numericOperator,
      NumericComparisonOp.holds]
  · simp [RootCurrentRepetitionComparison.eval,
      RootCurrentRepetitionComparison.numericOperator,
      NumericComparisonOp.evalFixedRight, NumericComparisonOp.eval,
      NumericComparisonOp.holds]

/-- The exact leaf is definitionally the direct filled guard conjoined with its closed constant-one comparison. -/
@[simp]
theorem validationCondition_guardedRootCurrentRepetition_evalSelected
    (model : FlatModel) (guard : FlatFieldDecl) (group : GroupPath)
    (comparison : RootCurrentRepetitionComparison)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    (ValidationCondition.guardedRootCurrentRepetition (model := model)
        guard group comparison).evalSelected context isRelevant =
      Verdict.conj
        (if isRelevant guard.id then
          guard.toPresenceField.evalFilled context.fields
        else
          .unknown)
        comparison.eval := by
  rfl

/-- Once the direct guard is relevant and filled, it is the conjunction identity and the leaf returns the exact constant-one comparison result. -/
theorem validationCondition_guardedRootCurrentRepetition_filled
    (model : FlatModel) (guard : FlatFieldDecl) (group : GroupPath)
    (comparison : RootCurrentRepetitionComparison)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance)
    (relevant : isRelevant guard.id = true)
    (filled : guard.toPresenceField.evalFilled context.fields = .fired .value) :
    (ValidationCondition.guardedRootCurrentRepetition (model := model)
        guard group comparison).evalSelected context isRelevant =
      comparison.eval := by
  simp [validationCondition_guardedRootCurrentRepetition_evalSelected,
    relevant, filled]
  exact Verdict.conj_fired_value_left comparison.eval

/-- Constant-one equality is not an unguarded truth: a relevant empty guard makes the indivisible leaf false. This is the nearest checked refutation of the unsafe guard-erasing account. -/
theorem validationCondition_guardedRootCurrentRepetition_empty
    (model : FlatModel) (guard : FlatFieldDecl) (group : GroupPath)
    (comparison : RootCurrentRepetitionComparison)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance)
    (relevant : isRelevant guard.id = true)
    (empty : guard.toPresenceField.evalFilled context.fields = .notFired) :
    (ValidationCondition.guardedRootCurrentRepetition (model := model)
        guard group comparison).evalSelected context isRelevant =
      .notFired := by
  simp [validationCondition_guardedRootCurrentRepetition_evalSelected,
    relevant, empty]
  exact Verdict.conj_notFired_left comparison.eval

/-- Analyze sees the direct guard as the leaf's only field dependency; the structural repetition operand contributes no field. -/
@[simp]
theorem validationCondition_guardedRootCurrentRepetition_referencesField
    (model : FlatModel) (guard : FlatFieldDecl) (group : GroupPath)
    (comparison : RootCurrentRepetitionComparison) (field : FieldId) :
    (ValidationCondition.guardedRootCurrentRepetition (model := model)
        guard group comparison).referencesField field =
      (guard.id == field) := by
  rfl

/-- The exact measured leaf deliberately refuses the partial-validation carrier instead of collapsing structural insufficiency into UNKNOWN. -/
@[simp]
theorem validationConditionLeaf_guardedRootCurrentRepetition_partialUnsupported
    (model : FlatModel) (guard : FlatFieldDecl) (group : GroupPath)
    (comparison : RootCurrentRepetitionComparison) :
    (ValidationConditionLeaf.guardedRootCurrentRepetition
      (model := model) guard group comparison).supportsAddressedPartial = false := by
  rfl

/-- Addressed evaluation reads the direct guard and the named model-owned coordinate, then delegates only their conjunction to the shared verdict tree. -/
theorem validationConditionLeaf_guardedRepeatableCurrentRepetition_evalAddressed
    (model : FlatModel) (guard : FlatFieldDecl)
    (group : RepeatableGroupDecl)
    (comparison : RepeatableCurrentRepetitionComparison)
    (context : AddressedValidationEvaluationContext model)
    (cell : CheckedCell) (coordinate : Nat)
    (readGuard : context.readCell context.outer guard.id = .ok cell)
    (readCoordinate : context.outer.bindingAt group.level = .ok coordinate) :
    (ValidationConditionLeaf.guardedRepeatableCurrentRepetition
        guard group comparison).evalAddressed context =
      .ok (Verdict.conj
        (RepeatableFieldPresenceOperator.filled.eval
          (observeCell .validation cell))
        (comparison.eval coordinate)) := by
  change (do
    let reachedCell ← context.readCell context.outer guard.id
    let reachedCoordinate ← context.outer.bindingAt group.level
      |>.mapError CheckedAddressingError.environment
    pure (Verdict.conj
      (RepeatableFieldPresenceOperator.filled.eval
        (observeCell .validation reachedCell))
      (comparison.eval reachedCoordinate))) = _
  rw [readGuard, readCoordinate]
  rfl

/-- The direct guard remains the only field dependency; the structural row coordinate contributes no field. -/
@[simp]
theorem validationCondition_guardedRepeatableCurrentRepetition_referencesField
    (model : FlatModel) (guard : FlatFieldDecl)
    (group : RepeatableGroupDecl)
    (comparison : RepeatableCurrentRepetitionComparison) (field : FieldId) :
    (ValidationCondition.guardedRepeatableCurrentRepetition (model := model)
        guard group comparison).referencesField field =
      (guard.id == field) := by
  rfl

/-- The repeatable leaf derives its ordinary iteration scope solely from the indivisible direct guard. -/
@[simp]
theorem validationCondition_guardedRepeatableCurrentRepetition_iterationScope
    (model : FlatModel) (guard : FlatFieldDecl)
    (group : RepeatableGroupDecl)
    (comparison : RepeatableCurrentRepetitionComparison) :
    (ValidationCondition.guardedRepeatableCurrentRepetition (model := model)
        guard group comparison).ordinaryIterationScope =
      .ok (some guard.repeatableScope) := by
  rfl

/-- Partial validation refuses the exact repeatable leaf structurally rather than converting a missing row binding to UNKNOWN. -/
@[simp]
theorem validationConditionLeaf_guardedRepeatableCurrentRepetition_partialUnsupported
    (model : FlatModel) (guard : FlatFieldDecl)
    (group : RepeatableGroupDecl)
    (comparison : RepeatableCurrentRepetitionComparison) :
    (ValidationConditionLeaf.guardedRepeatableCurrentRepetition
      (model := model) guard group comparison).supportsAddressedPartial = false := by
  rfl

end A12Kernel
