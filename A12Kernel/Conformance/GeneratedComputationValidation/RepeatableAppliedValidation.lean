import A12Kernel.Elaboration.GeneratedComputationAppliedValidation
import A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

/-! # Repeatable-source generated validation after scalar application -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.RepeatableAppliedValidation

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

private def prepared : PreparedFlatStringContext repeatableModel
    builtinStringPatternCompiler :=
  (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
    repeatableModel).toOption.get (by native_decide)

private def table? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation repeatableModel)) := do
  let operation ← repeatableAggregateOperation.toOption
  pure {
    targetField := target.id
    name := "computedRepeatableAggregate"
    alternatives := .singleton { operation }
    messagePlan
  }

private def firstFilledTable? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation repeatableModel)) := do
  let operation ← repeatableFirstFilledOperation.toOption
  pure {
    targetField := target.id
    name := "computedRepeatableFirstFilled"
    alternatives := .singleton { operation }
    messagePlan
  }

private def numberCell (field : FieldId) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def document? (targetValue : Option Int)
    (rows : List (RowIndex × Int)) : Option (CheckedDocument repeatableModel) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows.map fun row => { group := 10, path := [row.1] }
    cells := (targetValue.map (numberCell target.id [])).toList ++
      rows.map fun row => numberCell repeatedGate.id [row.1] row.2
  }).toOption

private def firstFilledDocument? (targetValue : Option Int)
    (firstGate firstValue secondGate secondValue : Int) :
    Option (CheckedDocument repeatableModel) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [1, 2].map fun row => { group := 10, path := [row] }
    cells := [numberCell gate.id [] 1] ++
      (targetValue.map (numberCell target.id [])).toList ++ [
        numberCell repeatedGate.id [1] firstGate,
        numberCell repeatedTarget.id [1] firstValue,
        numberCell repeatedGate.id [2] secondGate,
        numberCell repeatedTarget.id [2] secondValue]
  }).toOption

private def result? : Option
    (StoredNumber × NumericTargetState × FlatRuleOutcome) := do
  let table ← table?
  let source ← document? (some 9) [(1, 2), (2, 3)]
  let destination ← document? none [(1, 2), (2, 4)]
  let run ← (table.executeNumericAppliedValidation evaluationWorld
    evaluationWorld source destination (fun _ => ()) []).toOption
  let changed ← run.result.withChanges.head?
  pure (changed.value,
    run.applied.stateAt { field := target.id, path := [] }, run.validation)

/- Execution sums the immutable source rows to five and applies that value. Later
   validation rereads the differing destination rows, obtains six, and fires with
   the aggregate branch's established omission polarity. -/
example : result? = some (
    { unscaled := 5, scale := 0 },
    .presentValue (.decimal { unscaled := 5, scale := 0 }),
    .fired (repeatableExpectedMessage "computedRepeatableAggregate" .omission)) := by
  native_decide

private def filteredResult? : Option
    (StoredNumber × NumericTargetState × FlatRuleOutcome) := do
  let table ← firstFilledTable?
  let source ← firstFilledDocument? (some 9) 0 9 1 5
  let destination ← firstFilledDocument? none 1 6 1 5
  let run ← (table.executeNumericAppliedValidation evaluationWorld
    evaluationWorld source destination (fun _ => ()) []).toOption
  let changed ← run.result.withChanges.head?
  pure (changed.value,
    run.applied.stateAt { field := target.id, path := [] }, run.validation)

/- The source filter skips row one and selects five from row two. After application,
   the destination filter admits row one and the generated mismatch sees six. -/
example : filteredResult? = some (
    { unscaled := 5, scale := 0 },
    .presentValue (.decimal { unscaled := 5, scale := 0 }),
    .fired repeatableFirstFilledExpectedMessage) := by
  native_decide

end A12Kernel.Conformance.GeneratedComputationValidation.RepeatableAppliedValidation
