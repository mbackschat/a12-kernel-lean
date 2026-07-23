import A12Kernel.Elaboration.StringComputation

/-! # Checked String-computation lowering laws -/

namespace A12Kernel

/-- Decoded String literals pass through checked lowering unchanged. -/
theorem elaborateStringExprCore_literal (model : FlatModel)
    (declaringGroup : GroupPath) (value : String) :
    elaborateStringExprCore model declaringGroup (.literal value) =
      .ok (.literal value) := by
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
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) :
    expression.evaluate prepared locale raw =
      expression.core.evaluate {
        read := (prepared.checkContext locale raw).read
      } := by
  rfl

/-- A checked ordinary String operation retains the exact declaration-owned target relation. -/
theorem checkedStringComputation_target_admitted
    (operation : CheckedStringComputationOperation model) :
    model.admitsStringComputationTarget operation.targetField
      operation.targetPolicy = true :=
  operation.targetAdmitted

/-- Integrated String-operation lowering makes direct target self-reference unrepresentable. -/
theorem checkedStringComputation_excludes_target_reference
    (operation : CheckedStringComputationOperation model) :
    operation.expression.core.referencesField operation.targetField = false :=
  operation.targetNotReferenced

/-- The checked wrapper adds no second target evaluator: it composes the established expression evaluation with the shared declaration-owned target check. -/
theorem checkedStringComputation_evaluateOutcome
    (operation : CheckedStringComputationOperation model)
    (prepared : PreparedFlatStringContext model compilePattern)
    (locale : String) (raw : RawFlatContext) :
    operation.evaluateOutcome prepared locale raw = (do
      let store ← operation.expression.evaluate prepared locale raw
      pure (operation.targetPolicy.checkTarget store)) := by
  rfl

end A12Kernel
