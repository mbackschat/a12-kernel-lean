import A12Kernel.Conformance.ParallelComputationClearingPlan

/-! # Parallel Number scale-warning suppression locks

These cases distinguish the checked authoring directive from arithmetic recovery. The family fixture supplies the exact parallel route; the expression remains the established numeric tree.
-/

namespace A12Kernel.Conformance.ParallelNumericScaleSuppression

open A12Kernel
open A12Kernel.Conformance.ParallelComputationClearingPlan

private def divisionExpression (denominator : Rat) :
    AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .divide
    (.atom (.field operandPath))
    (.literal { value := denominator, authoredScale := 0 })

private def checked? (denominator : Rat)
    (suppressExactScaleWarning : Bool) :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] 2 operandPath (divisionExpression denominator) none
      suppressExactScaleWarning).toOption

private def outcomes? (denominator : Rat)
    (cells : List ClassifiedCellInput) :
    Option (List NumericTargetOutcome) := do
  let checked ← checked? denominator true
  let preliminary ← preliminaryFor cells
  let outcomes ← (checked.execute preliminary).toOption
  pure (outcomes.map (·.outcome))

example :
    (match checkIsolatedParallelNumericExpressionRunWithGuard
        model ["Plan"] 2 operandPath (divisionExpression 2) none false with
    | .error error => some error
    | .ok _ => none) =
      some (.operationScaleMismatch 0
        { scale := .unknown, canExpandScale := false }) := by
  native_decide

example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 }
    ]
    outcomes? 2 clean =
      some [
        .accepted { unscaled := 50, scale := 0 },
        .accepted { unscaled := 0, scale := 0 },
        .accepted { unscaled := 100, scale := 0 }
      ] := by
  native_decide

/- Warning suppression admits the unknown static scale; it does not turn a runtime-invalid quotient into a value. -/
example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 }
    ]
    outcomes? 0 clean =
      some [
        .invalidNoValue .calculationValue,
        .invalidNoValue .calculationValue,
        .invalidNoValue .calculationValue
      ] := by
  native_decide

end A12Kernel.Conformance.ParallelNumericScaleSuppression
