import A12Kernel.Elaboration.StringComputation

/-! # Checked String-computation lowering laws -/

namespace A12Kernel

/-- Decoded String literals pass through checked lowering unchanged. -/
theorem elaborateStringExprCore_literal (model : FlatModel)
    (declaringGroup : GroupPath) (value : String) :
    elaborateStringExprCore model declaringGroup (.literal value) =
      .ok (.literal value) := by
  rfl

/-- Successful `FieldValueAsString` lowering retains the dedicated coercion leaf around the resolved Number field. -/
theorem elaborateStringExprCore_fieldValueAsString (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath)
    (field : FieldId)
    (lowered :
      elaborateNumberAsStringField model declaringGroup reference = .ok field) :
    elaborateStringExprCore model declaringGroup
      (.fieldValueAsString reference) =
        .ok (.fieldValueAsString field) := by
  unfold elaborateStringExprCore
  rw [lowered]
  rfl

/-- A successfully lowered `RangeAsString` retains the exact authored interval around its resolved field leaf. -/
theorem elaborateStringExprCore_range (model : FlatModel)
    (declaringGroup : GroupPath) (reference : SurfaceFieldPath)
    (declaration : FlatFieldDecl) (field : FieldId) (start finish : Nat)
    (startPositive : 1 ≤ start) (ordered : start ≤ finish)
    (resolved :
      (model.resolveNonrepeatableFieldUnchecked declaringGroup reference).mapError
        StringComputationElabError.resolve = .ok declaration)
    (admitted : admitStringComputationValueField declaration = .ok field) :
    elaborateStringExprCore model declaringGroup (.range reference start finish) =
      .ok (.range field start finish) := by
  unfold elaborateStringExprCore
  rw [resolved]
  have positive : 0 < start := Nat.lt_of_lt_of_le Nat.zero_lt_one startPositive
  have valid : validStringRange start finish = true := by
    simp [validStringRange, positive, ordered]
  simp only [valid, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  change (do
    let value ← admitStringComputationValueField declaration
    pure (StringExpr.range value start finish)) =
      .ok (StringExpr.range field start finish)
  rw [admitted]
  rfl

/-- Successful child lowering preserves the authored concatenation shape and order exactly. -/
theorem elaborateStringExprCore_concat (model : FlatModel)
    (declaringGroup : GroupPath)
    (left right : StringExpr SurfaceFieldPath)
    (loweredLeft loweredRight : StringExpr FieldId)
    (leftOk : elaborateStringExprCore model declaringGroup left = .ok loweredLeft)
    (rightOk : elaborateStringExprCore model declaringGroup right = .ok loweredRight) :
    elaborateStringExprCore model declaringGroup (.concat left right) =
      .ok (.concat loweredLeft loweredRight) := by
  unfold elaborateStringExprCore
  rw [leftOk, rightOk]
  rfl

/-- The checked wrapper adds no evaluator: it delegates to the established runtime tree. -/
theorem checkedStringExpr_evaluate (expression : CheckedStringExpr model)
    (input : CheckedDocument model) :
    expression.evaluate input =
      expression.core.evaluate input.stringComputationContext := by
  rfl

/-- A checked ordinary String operation retains the exact declaration-owned target relation. -/
theorem checkedStringComputation_target_admitted
    (operation : CheckedStringComputationOperation model) :
    model.admitsStringComputationTarget operation.targetField
      operation.targetPolicy = true :=
  operation.targetAdmitted

/-- Checked String definitions retain a syntactically valid computation declaration group even when
their expression has no field operand. -/
theorem checkedStringComputation_declaringGroup_valid
    (operation : CheckedStringComputationOperation model) :
    GroupPath.isValid operation.declaringGroup = true :=
  operation.declaringGroupValid

/-- Integrated String-operation lowering makes direct target self-reference unrepresentable. -/
theorem checkedStringComputation_excludes_target_reference
    (operation : CheckedStringComputationOperation model) :
    operation.expression.core.referencesField operation.targetField = false :=
  operation.targetNotReferenced

/-- The checked wrapper adds no second target evaluator: once its exact prepared matcher is recovered, it composes the established expression evaluation with the shared declaration-owned target check. -/
theorem checkedStringComputation_evaluateOutcome
    (operation : CheckedStringComputationOperation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (matcher : Option (String → Bool))
    (preparedTarget :
      patterns.targetMatcher? operation.targetField = some matcher) :
    operation.evaluateOutcome patterns input = (do
      let store ← operation.expression.evaluate input
      pure (operation.targetPolicy.checkTargetWithPattern matcher store)) := by
  simp [CheckedStringComputationOperation.evaluateOutcome, preparedTarget]

/-- A forged or incomplete prepared target plan fails closed instead of silently treating a required declared pattern as absent. -/
theorem checkedStringComputation_missingTargetPattern_failsClosed
    (operation : CheckedStringComputationOperation model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (missing :
      patterns.targetMatcher? operation.targetField = none) :
    operation.evaluateOutcome patterns input =
      .error (.targetPatternUnavailable operation.targetField) := by
  unfold CheckedStringComputationOperation.evaluateOutcome
  rw [missing]
  rfl

end A12Kernel
