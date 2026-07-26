import A12Kernel.Conformance.ParallelComputationClearingPlan

/-! # Parallel Number same-group guard locks

These cases keep direct computation presence kind-neutral while requiring every bare guard ID to inhabit the already-selected operand-group environment.
-/

namespace A12Kernel.Conformance.ParallelNumericSameGroupGuard

open A12Kernel
open A12Kernel.Conformance.ParallelComputationClearingPlan

private def checked? :=
  (checkIsolatedParallelNumericDirectRunWithGuard
    model ["Plan"] 2 operandPath (some (.fieldFilled 3))).toOption

private def shortCircuitChecked? :=
  (checkIsolatedParallelNumericDirectRunWithGuard
    model ["Plan"] 2 operandPath
      (some (.or (.fieldFilled 3) (.fieldFilled 6)))).toOption

private def outcomes? (cells : List ClassifiedCellInput) :
    Option (List NumericTargetOutcome) := do
  let checked ← checked?
  let preliminary ← preliminaryFor cells
  let outcomes ← (checked.execute preliminary).toOption
  pure (outcomes.map (·.outcome))

private def shortCircuitHead? (cells : List ClassifiedCellInput) :
    Option NumericTargetOutcome := do
  let checked ← shortCircuitChecked?
  let preliminary ← preliminaryFor cells
  let outcomes ← (checked.execute preliminary).toOption
  outcomes.head?.map (·.outcome)

/- Presence of the String index field in the same matched operand row guards the Number operation without becoming a value operand. -/
example :
    let clean := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      operandNumericCell [2] { unscaled := 200, scale := 0 }
    ]
    outcomes? clean =
      some [
        .accepted { unscaled := 100, scale := 0 },
        .noValue,
        .accepted { unscaled := 200, scale := 0 }
      ] := by
  native_decide

/- Carrier lookup is not eager semantic observation: a holding left presence guard hides the malformed same-group field on its right. -/
example :
    let shortCircuit := cleanIndexCells ++ [
      operandNumericCell [1] { unscaled := 100, scale := 0 },
      { address := { field := 6, path := [1] },
        stored := "bad", raw := .rejected .malformed }
    ]
    shortCircuitHead? shortCircuit =
      some (.accepted { unscaled := 100, scale := 0 }) := by
  native_decide

end A12Kernel.Conformance.ParallelNumericSameGroupGuard
