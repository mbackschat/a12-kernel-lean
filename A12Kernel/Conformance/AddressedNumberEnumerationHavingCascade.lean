import A12Kernel.Elaboration.AddressedNumberEnumerationHavingCascade
import A12Kernel.Elaboration.RepeatableNumberAggregateProducer

/-! # Number dependency inside Enumeration `Having` locks -/

namespace A12Kernel.Conformance.AddressedNumberEnumerationHavingCascade

open A12Kernel

private def enumerationField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .enumeration }
  enumeration := some { storedTokens := ["A", "B"] }
}

private def numberField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := false } }
}

private def stringField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .string }
  stringPolicy := { lineBreaksPermitted := true, maxLength := some 6 }
}

private def target := enumerationField 1 "Target" ["Form", "Rows"] [10]
private def directChoice := enumerationField 2 "DirectChoice" ["Form", "Rows"] [10]
private def choice := enumerationField 3 "Choice" ["Form", "Rows", "Items"] [10, 20]
private def limit := numberField 4 "Limit" ["Form", "Rows"] [10]
private def computedGate := numberField 5 "ComputedGate" ["Form", "Rows", "Items"] [10, 20]
private def rawGate := numberField 6 "RawGate" ["Form", "Rows", "Items"] [10, 20]
private def text := stringField 7 "Text" ["Form", "Rows", "Items"] [10, 20]

private def model : FlatModel := {
  fields := [target, directChoice, choice, limit, computedGate, rawGate, text]
  repeatableGroups := [{
    level := 10
    path := ["Form", "Rows"]
    repeatability := some 2
  }, {
    level := 20
    path := ["Form", "Rows", "Items"]
    repeatability := some 2
  }]
}

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def numberRef (origin : HavingOrigin) (groups : List String)
    (field : String) : SurfaceHavingNumberRef := {
  origin
  field := { base := .absolute, groups, field }
}

private def selectedByComputedGate : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    (numberRef .inner ["Form", "Rows", "Items"] "ComputedGate")
    (numberRef .outer ["Form", "Rows"] "Limit")

private def selectedByRawGate : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    (numberRef .inner ["Form", "Rows", "Items"] "RawGate")
    (numberRef .outer ["Form", "Rows"] "Limit")

private def choiceStar (having : SurfaceCorrelatedHaving) :
    SurfaceEnumerationFirstFilledOperand :=
  .star {
    base := .absolute
    groups := [
      { name := "Form" },
      { name := "Rows" },
      { name := "Items", starred := true }]
    field := "Choice"
  } .stored (some having)

private def mixedSource (having : SurfaceCorrelatedHaving) :
    SurfaceEnumerationFirstFilledSource := {
  first := .field (.direct (bare "DirectChoice"))
  rest := [choiceStar having]
}

private def singleFilteredSource : SurfaceEnumerationFirstFilledSource := {
  first := choiceStar selectedByComputedGate
  rest := []
}

private def producer? : Option (CheckedAddressedNumberField model) :=
  (checkAddressedNumberField model ["Form", "Rows", "Items"]
    computedGate.id (bare "RawGate")).toOption

private def consumer? (having : SurfaceCorrelatedHaving) :
    Option (CheckedAddressedEnumerationFirstFilledComputation model) :=
  (checkAddressedEnumerationFirstFilledComputation model ["Form", "Rows"]
    target.id (mixedSource having)).toOption

private def plan? : Option (CheckedAddressedNumberEnumerationHavingCascade model) := do
  let producer ← producer?
  let consumer ← consumer? selectedByComputedGate
  (checkAddressedNumberEnumerationHavingCascade (.direct producer) consumer).toOption

private def stringLengthProducer? : Option (CheckedAddressedStringLength model) :=
  (checkAddressedStringLength model ["Form", "Rows", "Items"]
    computedGate.id (bare "Text")).toOption

private def stringLengthPlan? :
    Option (CheckedAddressedNumberEnumerationHavingCascade model) := do
  let producer ← stringLengthProducer?
  let consumer ← consumer? selectedByComputedGate
  (checkAddressedNumberEnumerationHavingCascade
    (.stringLength producer) consumer).toOption

private def planError? (having : SurfaceCorrelatedHaving) :
    Option AddressedNumberEnumerationHavingCascadeElabError := do
  let producer ← producer?
  let consumer ← consumer? having
  match checkAddressedNumberEnumerationHavingCascade (.direct producer) consumer with
  | .ok _ => none
  | .error cause => some cause

private def shapeError? :
    Option AddressedNumberEnumerationHavingCascadeElabError := do
  let producer ← producer?
  let consumer ←
    (checkAddressedEnumerationFirstFilledComputation model ["Form", "Rows"]
      target.id singleFilteredSource).toOption
  match checkAddressedNumberEnumerationHavingCascade (.direct producer) consumer with
  | .ok _ => none
  | .error cause => some cause

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def row (group : RepeatableLevel) (path : List Nat) : RowAddr :=
  { group, path }

private def cell (field : FlatFieldDecl) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput := {
  address := { field := field.id, path }
  stored
  raw
}

private def document? (rows : List RowAddr) (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def rows : List RowAddr := [
  row 10 [1], row 10 [2],
  row 20 [1, 1], row 20 [1, 2], row 20 [2, 1], row 20 [2, 2]]

private structure Summary where
  analysis : AddressedNumberEnumerationHavingCascadeAnalysis
  numbers : List (CellAddr × NumericDependencyObservation)
  enumerations : List (CellAddr × TokenComputationResult)
  deriving Repr, DecidableEq

private def summary? (input : CheckedDocument model) : Option Summary := do
  let plan ← plan?
  let outcomes ← plan.execute input |>.toOption
  pure {
    analysis := plan.analyze
    numbers := outcomes.producer.map fun outcome =>
      (outcome.targetField, outcome.outcome.dependencyObservation)
    enumerations := outcomes.consumer.map fun outcome =>
      (outcome.targetField, outcome.result)
  }

private def stringLengthSummary? (input : CheckedDocument model) : Option Summary := do
  let plan ← stringLengthPlan?
  let outcomes ← plan.execute input |>.toOption
  pure {
    analysis := plan.analyze
    numbers := outcomes.producer.map fun outcome =>
      (outcome.targetField, outcome.outcome.dependencyObservation)
    enumerations := outcomes.consumer.map fun outcome =>
      (outcome.targetField, outcome.result)
  }

/- The plan owns the complete checked dependency inventory and refuses both a filter without the producer edge and a broader source shape. -/
example :
    plan?.map CheckedAddressedNumberEnumerationHavingCascade.analyze = some {
      producerKind := .direct
      producerTarget := computedGate.id
      consumerTarget := target.id
      fieldDependencies := [
        (computedGate.id, [rawGate.id]),
        (target.id, [directChoice.id, choice.id, computedGate.id, limit.id])]
    } ∧
    planError? selectedByRawGate =
      some (.missingFilterDependency computedGate.id) ∧
    shapeError? = some .consumerSourceShape := by
  native_decide

/- Fresh row outcomes replace stale computed seeds inside `Having`; a poisoned producer remains hidden when the direct first operand already decides the consumer. -/
example : (do
    let input ← document? rows [
      cell directChoice [1] "A" (.parsed (.enum "A")),
      cell limit [1] "1" (.parsed (.num 1)),
      cell limit [2] "2" (.parsed (.num 2)),
      cell rawGate [1, 1] "bad" (.rejected .malformed),
      cell rawGate [1, 2] "0" (.parsed (.num 0)),
      cell rawGate [2, 1] "1" (.parsed (.num 1)),
      cell rawGate [2, 2] "2" (.parsed (.num 2)),
      cell computedGate [1, 1] "1" (.parsed (.num 1)),
      cell computedGate [2, 1] "2" (.parsed (.num 2)),
      cell computedGate [2, 2] "1" (.parsed (.num 1)),
      cell choice [1, 1] "B" (.parsed (.enum "B")),
      cell choice [2, 1] "A" (.parsed (.enum "A")),
      cell choice [2, 2] "B" (.parsed (.enum "B"))]
    summary? input) = some {
      analysis := {
        producerKind := .direct
        producerTarget := computedGate.id
        consumerTarget := target.id
        fieldDependencies := [
          (computedGate.id, [rawGate.id]),
          (target.id, [directChoice.id, choice.id, computedGate.id, limit.id])]
      }
      numbers := [
        ({ field := computedGate.id, path := [1, 1] }, .poisoned),
        ({ field := computedGate.id, path := [1, 2] }, .value { unscaled := 0, scale := 0 }),
        ({ field := computedGate.id, path := [2, 1] }, .value { unscaled := 1, scale := 0 }),
        ({ field := computedGate.id, path := [2, 2] }, .value { unscaled := 2, scale := 0 })]
      enumerations := [
        ({ field := target.id, path := [1] }, .value "A"),
        ({ field := target.id, path := [2] }, .value "B")]
    } := by
  native_decide

/- Once the direct prefix is empty, the same completed poison is reached by `Having` and clears the lazy first-filled result through the cause-blind dependency channel. -/
example : (do
    let input ← document? [row 10 [1], row 20 [1, 1]] [
      cell limit [1] "1" (.parsed (.num 1)),
      cell rawGate [1, 1] "bad" (.rejected .malformed),
      cell computedGate [1, 1] "1" (.parsed (.num 1)),
      cell choice [1, 1] "A" (.parsed (.enum "A"))]
    let result ← summary? input
    pure result.enumerations) = some [
      ({ field := target.id, path := [1] }, .poison .computedDependency)] := by
  native_decide

/- The already checked UTF-16 String-length producer supplies the filter dependency through the same Number overlay. Fresh length 2 defeats reversed stale gates, a reached malformed String becomes cause-blind dependency poison, and the direct prefix hides that same completed poison. -/
example : (do
    let fresh ← document? [row 10 [1], row 20 [1, 1], row 20 [1, 2]] [
      cell limit [1] "2" (.parsed (.num 2)),
      cell text [1, 1] "😀" (.parsed (.str "😀")),
      cell text [1, 2] "X" (.parsed (.str "X")),
      cell computedGate [1, 1] "0" (.parsed (.num 0)),
      cell computedGate [1, 2] "2" (.parsed (.num 2)),
      cell choice [1, 1] "B" (.parsed (.enum "B")),
      cell choice [1, 2] "A" (.parsed (.enum "A"))]
    let poisoned ← document? [row 10 [1], row 20 [1, 1]] [
      cell limit [1] "2" (.parsed (.num 2)),
      cell text [1, 1] "bad" (.rejected .malformed),
      cell computedGate [1, 1] "2" (.parsed (.num 2)),
      cell choice [1, 1] "A" (.parsed (.enum "A"))]
    let hidden ← document? [row 10 [1], row 20 [1, 1]] [
      cell directChoice [1] "A" (.parsed (.enum "A")),
      cell limit [1] "2" (.parsed (.num 2)),
      cell text [1, 1] "bad" (.rejected .malformed),
      cell computedGate [1, 1] "2" (.parsed (.num 2)),
      cell choice [1, 1] "B" (.parsed (.enum "B"))]
    let freshSummary ← stringLengthSummary? fresh
    let poisonedSummary ← stringLengthSummary? poisoned
    let hiddenSummary ← stringLengthSummary? hidden
    pure (freshSummary, poisonedSummary.enumerations,
      hiddenSummary.enumerations)) = some ({
      analysis := {
        producerKind := .stringLength
        producerTarget := computedGate.id
        consumerTarget := target.id
        fieldDependencies := [
          (computedGate.id, [text.id]),
          (target.id, [directChoice.id, choice.id, computedGate.id, limit.id])]
      }
      numbers := [
        ({ field := computedGate.id, path := [1, 1] },
          .value { unscaled := 2, scale := 0 }),
        ({ field := computedGate.id, path := [1, 2] },
          .value { unscaled := 1, scale := 0 })]
      enumerations := [
        ({ field := target.id, path := [1] }, .value "B")]
    }, [
      ({ field := target.id, path := [1] }, .poison .computedDependency)], [
      ({ field := target.id, path := [1] }, .value "A")]) := by
  native_decide

private def numericCell (field : FlatFieldDecl) (path : List Nat)
    (stored : String) (value : Int) : ClassifiedCellInput := {
  address := { field := field.id, path }
  stored
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private structure ResultApplicationSummary where
  numberValues : List (CellAddr × StoredNumber)
  numberChanges : List (CellAddr × StoredNumber)
  numberCleared : List CellAddr
  enumerationValues : List (CellAddr × String)
  enumerationChanges : List (CellAddr × String)
  enumerationCleared : List CellAddr
  enumerationErrorTargets : List CellAddr
  gate11 : NumericTargetState
  gate12 : NumericTargetState
  gate21 : NumericTargetState
  gate22 : NumericTargetState
  target1 : StringTargetState
  target2 : StringTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? (input destination : CheckedDocument model) :
    Option ResultApplicationSummary := do
  let plan ← plan?
  let view ← plan.executeResult input (fun _ => ()) []
    ([] : List Unit) |>.toOption
  let numberApplied ← view.number.applyToChecked destination |>.toOption
  let enumerationApplied ←
    view.enumeration.applyToChecked destination |>.toOption
  pure {
    numberValues := view.number.withoutErrors.map fun item =>
      (item.targetField, item.value)
    numberChanges := view.number.withChanges.map fun item =>
      (item.targetField, item.value)
    numberCleared := view.number.cleared
    enumerationValues := view.enumeration.string.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    enumerationChanges := view.enumeration.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    enumerationCleared := view.enumeration.string.cleared
    enumerationErrorTargets := view.enumeration.string.withErrors.map
      (fun item => item.targetField)
    gate11 := numberApplied.stateAt { field := computedGate.id, path := [1, 1] }
    gate12 := numberApplied.stateAt { field := computedGate.id, path := [1, 2] }
    gate21 := numberApplied.stateAt { field := computedGate.id, path := [2, 1] }
    gate22 := numberApplied.stateAt { field := computedGate.id, path := [2, 2] }
    target1 := enumerationApplied { field := target.id, path := [1] }
    target2 := enumerationApplied { field := target.id, path := [2] }
  }

private def resultInput? : Option (CheckedDocument model) :=
  document? rows [
    cell directChoice [1] "A" (.parsed (.enum "A")),
    numericCell limit [1] "1" 1,
    numericCell limit [2] "2" 2,
    cell rawGate [1, 1] "bad" (.rejected .malformed),
    numericCell rawGate [1, 2] "0" 0,
    numericCell rawGate [2, 1] "1" 1,
    numericCell rawGate [2, 2] "2" 2,
    numericCell computedGate [1, 1] "9" 9,
    numericCell computedGate [2, 1] "1" 1,
    numericCell computedGate [2, 2] "1" 1,
    cell choice [1, 1] "B" (.parsed (.enum "B")),
    cell choice [2, 1] "A" (.parsed (.enum "A")),
    cell choice [2, 2] "B" (.parsed (.enum "B")),
    cell target [1] "A" (.parsed (.enum "A")),
    cell target [2] "A" (.parsed (.enum "A"))]

private def resultDestination? : Option (CheckedDocument model) :=
  document? rows [
    numericCell computedGate [1, 1] "7" 7,
    numericCell computedGate [1, 2] "8" 8,
    numericCell computedGate [2, 1] "8" 8,
    numericCell computedGate [2, 2] "8" 8,
    cell target [1] "B" (.parsed (.enum "B")),
    cell target [2] "A" (.parsed (.enum "A"))]

/- Both sourced phases classify independently and apply through their existing family owners. Source-identical successes remain inert against a different destination. -/
example : (do
    let input ← resultInput?
    let destination ← resultDestination?
    resultApplicationSummary? input destination) = some {
      numberValues := [
        ({ field := computedGate.id, path := [1, 2] },
          { unscaled := 0, scale := 0 }),
        ({ field := computedGate.id, path := [2, 1] },
          { unscaled := 1, scale := 0 }),
        ({ field := computedGate.id, path := [2, 2] },
          { unscaled := 2, scale := 0 })]
      numberChanges := [
        ({ field := computedGate.id, path := [1, 2] },
          { unscaled := 0, scale := 0 }),
        ({ field := computedGate.id, path := [2, 2] },
          { unscaled := 2, scale := 0 })]
      numberCleared := [{ field := computedGate.id, path := [1, 1] }]
      enumerationValues := [
        ({ field := target.id, path := [1] }, "A"),
        ({ field := target.id, path := [2] }, "B")]
      enumerationChanges := [({ field := target.id, path := [2] }, "B")]
      enumerationCleared := []
      enumerationErrorTargets := []
      gate11 := .presentEmpty
      gate12 := .presentValue (.decimal { unscaled := 0, scale := 0 })
      gate21 := .presentValue (.decimal { unscaled := 8, scale := 0 })
      gate22 := .presentValue (.decimal { unscaled := 2, scale := 0 })
      target1 := .presentValue ⟨"B", by decide⟩
      target2 := .presentValue ⟨"B", by decide⟩
    } := by
  native_decide

end A12Kernel.Conformance.AddressedNumberEnumerationHavingCascade
