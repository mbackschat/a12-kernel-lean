import A12Kernel.Elaboration.AddressedNumberEnumerationHavingCascade

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

private def target := enumerationField 1 "Target" ["Form", "Rows"] [10]
private def directChoice := enumerationField 2 "DirectChoice" ["Form", "Rows"] [10]
private def choice := enumerationField 3 "Choice" ["Form", "Rows", "Items"] [10, 20]
private def limit := numberField 4 "Limit" ["Form", "Rows"] [10]
private def computedGate := numberField 5 "ComputedGate" ["Form", "Rows", "Items"] [10, 20]
private def rawGate := numberField 6 "RawGate" ["Form", "Rows", "Items"] [10, 20]

private def model : FlatModel := {
  fields := [target, directChoice, choice, limit, computedGate, rawGate]
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
  (checkAddressedNumberEnumerationHavingCascade producer consumer).toOption

private def planError? (having : SurfaceCorrelatedHaving) :
    Option AddressedNumberEnumerationHavingCascadeElabError := do
  let producer ← producer?
  let consumer ← consumer? having
  match checkAddressedNumberEnumerationHavingCascade producer consumer with
  | .ok _ => none
  | .error cause => some cause

private def shapeError? :
    Option AddressedNumberEnumerationHavingCascadeElabError := do
  let producer ← producer?
  let consumer ←
    (checkAddressedEnumerationFirstFilledComputation model ["Form", "Rows"]
      target.id singleFilteredSource).toOption
  match checkAddressedNumberEnumerationHavingCascade producer consumer with
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

/- The plan owns the complete checked dependency inventory and refuses both a filter without the producer edge and a broader source shape. -/
example :
    plan?.map CheckedAddressedNumberEnumerationHavingCascade.analyze = some {
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

end A12Kernel.Conformance.AddressedNumberEnumerationHavingCascade
