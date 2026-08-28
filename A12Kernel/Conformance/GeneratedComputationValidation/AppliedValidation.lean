import A12Kernel.Elaboration.GeneratedComputationAppliedValidation
import A12Kernel.Conformance.GeneratedComputationValidation.Support.CrossGroup

/-! # Generated-computation application followed by generated validation -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.AppliedValidation

open A12Kernel
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Core
open A12Kernel.Conformance.GeneratedComputationValidation.Support.Repeatable

private def literalOperation (value : Int) :
    Except NumericComputationElabError
      (CheckedNumericComputationOperation model) :=
  elaborateNumericComputationOperation model ["Rules"] target.id
    (.literal { value, authoredScale := 0 })

private def overlappingTable? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation model)) := do
  let first ← (literalOperation 1).toOption
  let second ← (literalOperation 2).toOption
  pure {
    targetField := target.id
    name := "computedTarget"
    alternatives := .guarded {
      first := { precondition := .fieldFilled gate.id, operation := first }
      second := { precondition := .fieldFilled gate.id, operation := second }
    }
    messagePlan
  }

private def singletonTable? (precondition : Option ComputationCondition := none) :
    Option (GeneratedComputationTable
      (CheckedNumericComputationOperation model)) := do
  let operation ← (literalOperation 1).toOption
  pure {
    targetField := target.id
    name := "computedTarget"
    alternatives := .singleton { precondition, operation }
    messagePlan
  }

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler model)
    |>.toOption.get (by native_decide)

private def numberCell (field : FieldId) (value : Int) :
    ClassifiedCellInput := {
  address := { field, path := [] }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def document? (gateValue targetValue : Option Int) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells :=
      (gateValue.map (numberCell gate.id)).toList ++
        (targetValue.map (numberCell target.id)).toList
  }).toOption

private structure Observation where
  changes : List StoredNumber
  cleared : List CellAddr
  applied : NumericTargetState
  validation : FlatRuleOutcome
  deriving Repr, DecidableEq

private def observe? (table : GeneratedComputationTable
    (CheckedNumericComputationOperation model))
    (sourceGate sourceTarget destinationGate destinationTarget : Option Int) :
    Option Observation := do
  let source ← document? sourceGate sourceTarget
  let destination ← document? destinationGate destinationTarget
  let run ← (table.executeNumericAppliedValidation evaluationWorld
    evaluationWorld source destination (fun _ => ()) []).toOption
  pure {
    changes := run.result.withChanges.map (·.value)
    cleared := run.result.cleared
    applied := run.applied.stateAt { field := target.id, path := [] }
    validation := run.validation
  }

private def overlappingResult? : Option Observation := do
  let table ← overlappingTable?
  observe? table (some 7) (some 9) (some 7) none

private def destinationGuardResult? : Option Observation := do
  let table ← overlappingTable?
  observe? table (some 7) (some 9) none none

/- Application creates the absent destination target with the first selected
   value before every holding validation alternative, so the later mismatch fires. -/
example : overlappingResult? = some {
    changes := [{ unscaled := 1, scale := 0 }]
    cleared := []
    applied := .presentValue (.decimal { unscaled := 1, scale := 0 })
    validation := .fired (expectedMessage .value)
  } := by
  native_decide

/- Execution selects from the source, but later scalar guards read the applied
   destination. Its absent guard therefore suppresses the generated mismatch. -/
example : destinationGuardResult? = some {
    changes := [{ unscaled := 1, scale := 0 }]
    cleared := []
    applied := .presentValue (.decimal { unscaled := 1, scale := 0 })
    validation := .notFired
  } := by
  native_decide

private def singletonChangedResult? : Option Observation := do
  let table ← singletonTable?
  observe? table none (some 9) none (some 2)

/- Validation reads the applied value rather than the stale destination value. -/
example : singletonChangedResult? = some {
    changes := [{ unscaled := 1, scale := 0 }]
    cleared := []
    applied := .presentValue (.decimal { unscaled := 1, scale := 0 })
    validation := .notFired
  } := by
  native_decide

private def clearedResult? : Option Observation := do
  let table ← singletonTable? (some (.fieldFilled gate.id))
  observe? table none (some 9) (some 7) (some 2)

/- A source-relative no-match clear empties the destination before the generated
   target-filled gate runs; the stale destination value cannot fire. -/
example : clearedResult? = some {
    changes := []
    cleared := [{ field := target.id, path := [] }]
    applied := .presentEmpty
    validation := .notFired
  } := by
  native_decide

private def crossGroupPrepared : PreparedFlatStringContext crossGroupModel
    builtinStringPatternCompiler :=
  (prepareFlatStringContext evaluationWorld builtinStringPatternCompiler
    crossGroupModel).toOption.get (by native_decide)

private def crossGroupNumberTable? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation crossGroupModel)) := do
  let operation ← crossGroupNumberOperation.toOption
  pure {
    targetField := crossGroupTarget.id
    name := "copiedTarget"
    alternatives := .singleton { operation }
    messagePlan
  }

private def crossGroupNumberDocument? (source target : Option Int) :
    Option (CheckedDocument crossGroupModel) :=
  (checkDocument crossGroupPrepared "en_US" {
    instantiatedRows := []
    cells :=
      (source.map (numberCell crossGroupSource.id)).toList ++
        (target.map (numberCell crossGroupTarget.id)).toList
  }).toOption

private def destinationOperandResult? : Option (NumericTargetState × FlatRuleOutcome) := do
  let table ← crossGroupNumberTable?
  let source ← crossGroupNumberDocument? (some 3) (some 9)
  let destination ← crossGroupNumberDocument? (some 4) none
  let run ← (table.executeNumericAppliedValidation evaluationWorld
    evaluationWorld source destination (fun _ => ()) []).toOption
  pure (run.applied.stateAt { field := crossGroupTarget.id, path := [] },
    run.validation)

/- The applied target keeps the source-derived result, while its generated
   mismatch recomputes addressed operands from the destination. -/
example : destinationOperandResult? = some (
    .presentValue (.decimal { unscaled := 3, scale := 0 }),
    .fired {
      errorAddress := MessagePointer.ofCellAddr {
        field := crossGroupTarget.id, path := [] }
      errorCode := "copiedTarget"
      severity := .error
      messageType := .value
      text
    }) := by
  native_decide

private def clockTable? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation crossGroupModel)) := do
  let operation ← crossGroupNowDifferenceOperation.toOption
  pure {
    targetField := crossGroupTarget.id
    name := "clockTarget"
    alternatives := .singleton { operation }
    messagePlan
  }

private def clockDocument? : Option (CheckedDocument crossGroupModel) := do
  let clock ← TimeOfDay.ofHms? 1 0 0
  (checkDocument crossGroupPrepared "en_US" {
    instantiatedRows := []
    cells := [
      {
        address := { field := crossGroupDateTime.id, path := [] }
        stored := "1970-01-01T01:00:00"
        raw := .parsed (.temporal (.dateTime { epochMillis := 0 }
          { year := 1970, month := 1, day := 1 } clock .storedGregorian))
      },
      numberCell crossGroupTarget.id 9
    ]
  }).toOption

private def clockValidationAt? (validationMillis : Int) :
    Option FlatRuleOutcome := do
  let table ← clockTable?
  let document ← clockDocument?
  let run ← (table.executeNumericAppliedValidation
    { now := { epochMillis := 1000 } }
    { now := { epochMillis := validationMillis } }
    document document (fun _ => ()) []).toOption
  pure run.validation

private def clockExpectedMessage : FlatRuleMessage := {
  errorAddress := MessagePointer.ofCellAddr {
    field := crossGroupTarget.id, path := [] }
  errorCode := "clockTarget"
  severity := .error
  messageType := .value
  text
}

/- Generated validation receives its own later world: the applied one-second
   result agrees at the execution instant and disagrees one second later. -/
example : clockValidationAt? 1000 = some .notFired ∧
    clockValidationAt? 2000 = some (.fired clockExpectedMessage) := by
  native_decide

end A12Kernel.Conformance.GeneratedComputationValidation.AppliedValidation
