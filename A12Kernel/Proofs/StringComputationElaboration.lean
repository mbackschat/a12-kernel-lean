import A12Kernel.Elaboration.StringComputation

/-! # Checked String-computation lowering laws -/

namespace A12Kernel

/-- Decoded String literals pass through checked lowering unchanged. -/
theorem elaborateStringExprCore_literal (model : FlatModel)
    (declaringGroup : GroupPath) (value : String) :
    elaborateStringExprCore model declaringGroup (.literal value) =
      .ok (.literal value) := by
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
    (raw : RawFlatContext) :
    expression.evaluate raw =
      expression.core.evaluate { read := (model.checkContext raw).read } := by
  rfl

end A12Kernel
