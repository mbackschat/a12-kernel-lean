import A12Kernel.Conformance.ParallelComputationClearingPlan

/-! # Parallel Number same-group operand locks

These cases require two distinct Number atoms to use one already-selected operand-group environment. The field identity remains observable even though the index join is shared.
-/

namespace A12Kernel.Conformance.ParallelNumericJoinedOperands

open A12Kernel
open A12Kernel.Conformance.ParallelComputationClearingPlan

private def offsetPath : SurfaceFieldPath :=
  { operandPath with field := "Offset" }

private def sumExpression : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add
    (.atom (.field operandPath))
    (.atom (.field offsetPath))

private def checked? :=
  (checkIsolatedParallelNumericExpressionRunWithGuard
    model ["Plan"] 2 operandPath sumExpression none).toOption

private def offsetNumericCell (path : List Nat) (stored : StoredNumber) :
    ClassifiedCellInput := {
  address := { field := 6, path }
  stored := stored.render
  raw := .parsed (.num stored.amount)
}

private def rejectedNumericCell (field : FieldId) (path : List Nat)
    (cause : BaseFormalCause) : ClassifiedCellInput := {
  address := { field, path }
  stored := match cause with
    | .declaredConstraint => "-1"
    | _ => "bad"
  raw := .rejected cause
}

private def outcomes? (cells : List ClassifiedCellInput) :
    Option (List NumericTargetOutcome) := do
  let checked ← checked?
  let preliminary ← preliminaryFor cells
  let outcomes ← (checked.execute preliminary).toOption
  pure (outcomes.map (·.outcome))

/- One indexed group retains one route even when the expression reads several fields from it. -/
example :
    checked?.map (·.additionalRoutes.length) = some 0 := by
  native_decide

/- Distinct fields in the same matched operand row retain their identities; an unmatched target key supplies zero for both. -/
example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 },
      offsetNumericCell [1] { unscaled := 5, scale := 0 },
      offsetNumericCell [2] { unscaled := 7, scale := 0 }
    ]
    outcomes? clean =
      some [
        .accepted { unscaled := 105, scale := 0 },
        .accepted { unscaled := 0, scale := 0 },
        .accepted { unscaled := 207, scale := 0 }
      ] := by
  native_decide

/- Fetching both checked carriers does not observe them eagerly: the shared expression evaluator still reports the first authored poison. -/
example :
    let invalid := cleanIndexCells ++ [
      rejectedNumericCell 4 [1] .malformed,
      rejectedNumericCell 6 [1] .declaredConstraint,
      operandNumericCell [2] { unscaled := 200, scale := 0 },
      offsetNumericCell [2] { unscaled := 7, scale := 0 }
    ]
    (outcomes? invalid).bind (·.head?) =
      some (.inheritedPoison .malformed) := by
  native_decide

end A12Kernel.Conformance.ParallelNumericJoinedOperands
