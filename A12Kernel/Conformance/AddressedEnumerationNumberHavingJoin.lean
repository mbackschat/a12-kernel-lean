import A12Kernel.Elaboration.AddressedEnumerationNumberHavingJoin

/-! # Computed Enumeration value plus Number `Having` locks -/

namespace A12Kernel.Conformance.AddressedEnumerationNumberHavingJoin

open A12Kernel

private def enumerationField (id : FieldId) (name : String)
    (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath := path, repeatableScope := scope
  policy := { kind := .enumeration }
  enumeration := some { storedTokens := ["A", "B"] }
}

private def numberField (id : FieldId) (name : String)
    (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath := path, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := false } }
}

private def target := enumerationField 1 "Target" ["Form", "Rows"] [10]
private def directChoice := enumerationField 2 "DirectChoice" ["Form", "Rows"] [10]
private def rawChoice := enumerationField 3 "RawChoice" ["Form", "Rows", "Items"] [10, 20]
private def computedChoice : FlatFieldDecl := {
  enumerationField 4 "ComputedChoice" ["Form", "Rows", "Items"] [10, 20] with
  enumeration := some {
    storedTokens := ["A", "B"]
    categories := [{ name := "Numeric", tokens := ["1", "2"] }]
  }
}
private def otherChoice : FlatFieldDecl := {
  computedChoice with id := 8, name := "OtherChoice"
}
private def limit := numberField 5 "Limit" ["Form", "Rows"] [10]
private def rawGate := numberField 6 "RawGate" ["Form", "Rows", "Items"] [10, 20]
private def computedGate := numberField 7 "ComputedGate" ["Form", "Rows", "Items"] [10, 20]

private def model : FlatModel := {
  fields := [target, directChoice, rawChoice, computedChoice, limit, rawGate,
    computedGate, otherChoice]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 5 },
    { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 2 }]
}

private def bare (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

private def absolute (groups : List String) (name : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field := name }

private def numberRef (origin : HavingOrigin) (groups : List String)
    (name : String) : SurfaceHavingNumberRef :=
  { origin, field := absolute groups name }

private def having (inner : String) : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    (numberRef .inner ["Form", "Rows", "Items"] inner)
    (numberRef .outer ["Form", "Rows"] "Limit")

private def star (selected : String) (filter : SurfaceCorrelatedHaving) :
    SurfaceEnumerationFirstFilledOperand :=
  .star {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows" },
      { name := "Items", starred := true }]
    field := selected
  } .stored (some filter)

private def source (selected : String) (filter : SurfaceCorrelatedHaving) :
    SurfaceEnumerationFirstFilledSource := {
  first := .field (.direct (bare "DirectChoice"))
  rest := [star selected filter]
}

private def numberProducer? : Option (CheckedAddressedNumberField model) :=
  (checkAddressedNumberField model ["Form", "Rows", "Items"] computedGate.id
    (bare "RawGate")).toOption

private def enumerationProducer? (sourcePath := bare "RawChoice") :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows", "Items"]
    computedChoice.id (.field (.direct sourcePath))).toOption

private def enumerationLiteralProducer? :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows", "Items"]
    computedChoice.id (.literal "A")).toOption

private def consumer? (authored : SurfaceEnumerationFirstFilledSource) :
    Option (CheckedAddressedEnumerationFirstFilledComputation model) :=
  (checkAddressedEnumerationFirstFilledComputation model ["Form", "Rows"]
    target.id authored).toOption

private def plan? : Option (CheckedAddressedEnumerationNumberHavingJoin model) := do
  let numberProducer ← numberProducer?
  let enumerationProducer ← enumerationProducer?
  let consumer ← consumer? (source "ComputedChoice" (having "ComputedGate"))
  (checkAddressedEnumerationNumberHavingJoin numberProducer enumerationProducer
    consumer).toOption

private def error? (enumerationProducer := enumerationProducer?)
    (authored := source "ComputedChoice" (having "ComputedGate")) :
    Option AddressedEnumerationNumberHavingJoinElabError := do
  let numberProducer ← numberProducer?
  let enumerationProducer ← enumerationProducer
  let consumer ← consumer? authored
  match checkAddressedEnumerationNumberHavingJoin numberProducer enumerationProducer
      consumer with
  | .ok _ => none
  | .error cause => some cause

private def prepared : PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def row (group : RepeatableLevel) (path : List Nat) : RowAddr :=
  { group, path }

private def cell (field : FlatFieldDecl) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field := field.id, path }, stored, raw }

private def numericCell (field : FlatFieldDecl) (path : List Nat)
    (stored : String) (value : Int) : ClassifiedCellInput := {
  address := { field := field.id, path }
  stored
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def rows : List RowAddr :=
  [1, 2, 3, 4, 5].flatMap fun index =>
    [row 10 [index], row 20 [index, 1]] ++
      if index == 4 then [row 20 [index, 2]] else []

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells := [
    cell directChoice [1] "A" (.parsed (.enum "A")),
    numericCell limit [1] "1" 1, numericCell limit [2] "2" 2,
    numericCell limit [3] "3" 3, numericCell limit [4] "1" 1,
    numericCell limit [5] "1" 1,
    cell rawGate [1, 1] "bad" (.rejected .malformed),
    numericCell rawGate [2, 1] "2" 2, numericCell rawGate [3, 1] "1" 1,
    cell rawGate [4, 1] "bad" (.rejected .malformed),
    numericCell rawGate [4, 2] "0" 0,
    numericCell rawGate [5, 1] "1" 1,
    numericCell computedGate [1, 1] "1" 1,
    numericCell computedGate [2, 1] "1" 1,
    numericCell computedGate [3, 1] "3" 3,
    numericCell computedGate [4, 1] "1" 1,
    numericCell computedGate [4, 2] "0" 0,
    numericCell computedGate [5, 1] "1" 1,
    cell rawChoice [1, 1] "C" (.parsed (.enum "C")), cell rawChoice [2, 1] "B" (.parsed (.enum "B")),
    cell rawChoice [3, 1] "C" (.parsed (.enum "C")), cell rawChoice [4, 1] "B" (.parsed (.enum "B")),
    cell rawChoice [5, 1] "C" (.parsed (.enum "C")),
    cell computedChoice [1, 1] "B" (.parsed (.enum "B")),
    cell computedChoice [2, 1] "A" (.parsed (.enum "A")),
    cell computedChoice [3, 1] "A" (.parsed (.enum "A")),
    cell computedChoice [4, 1] "B" (.parsed (.enum "B")),
    cell computedChoice [4, 2] "B" (.parsed (.enum "B")),
    cell computedChoice [5, 1] "A" (.parsed (.enum "A")),
    cell target [1] "A" (.parsed (.enum "A")),
    cell target [2] "A" (.parsed (.enum "A")),
    cell target [3] "B" (.parsed (.enum "B")),
    cell target [4] "B" (.parsed (.enum "B"))] }).toOption

private structure Summary where
  analysis : AddressedEnumerationNumberHavingJoinAnalysis
  numbers : List (CellAddr × NumericDependencyObservation)
  enumerationProducer : List (CellAddr × TokenComputationResult)
  consumer : List (CellAddr × TokenComputationResult)
  deriving Repr, DecidableEq

private def summary? : Option Summary := do
  let plan ← plan?
  let input ← input?
  let outcomes ← plan.execute input |>.toOption
  pure {
    analysis := plan.analyze
    numbers := outcomes.numberProducer.map fun item =>
      (item.targetField, item.outcome.dependencyObservation)
    enumerationProducer := outcomes.enumerationProducer.map fun item =>
      (item.targetField, item.result)
    consumer := outcomes.consumer.map fun item => (item.targetField, item.result)
  }

/- Exact source and edge admission rejects either stale-input route and the reverse Enumeration edge. -/
example : plan?.isSome = true ∧
    error? (enumerationProducer := enumerationLiteralProducer?) =
      some .enumerationProducerSourceShape ∧
    error? (authored := source "RawChoice" (having "ComputedGate")) =
      some .missingEnumerationValueDependency ∧
    error? (authored := source "ComputedChoice" (having "RawGate")) =
      some .missingNumberFilterDependency ∧
    error? (enumerationProducer := enumerationProducer?
      (absolute ["Form", "Rows"] "Target")) =
      some .enumerationProducerReadsConsumer := by
  native_decide

/- Both independent overlays are fresh, direct selection hides both poisons, `Having` filters before reading a selected poison, and reached poison stays cause-blind. -/
example : summary? = some {
  analysis := {
      numberProducerTarget := computedGate.id
      enumerationProducerTarget := computedChoice.id
      consumerTarget := target.id
      fieldDependencies := [
        (computedGate.id, [rawGate.id]),
        (computedChoice.id, [rawChoice.id]),
        (target.id, [directChoice.id, computedChoice.id, computedGate.id,
          limit.id])]
    }
  numbers := [
    ({ field := computedGate.id, path := [1, 1] }, .poisoned),
    ({ field := computedGate.id, path := [2, 1] },
      .value { unscaled := 2, scale := 0 }),
    ({ field := computedGate.id, path := [3, 1] },
      .value { unscaled := 1, scale := 0 }),
    ({ field := computedGate.id, path := [4, 1] }, .poisoned),
    ({ field := computedGate.id, path := [4, 2] },
      .value { unscaled := 0, scale := 0 }),
    ({ field := computedGate.id, path := [5, 1] },
      .value { unscaled := 1, scale := 0 })]
  enumerationProducer := [
    ({ field := computedChoice.id, path := [1, 1] },
      .poison .declaredConstraint),
    ({ field := computedChoice.id, path := [2, 1] }, .value "B"),
    ({ field := computedChoice.id, path := [3, 1] },
      .poison .declaredConstraint),
    ({ field := computedChoice.id, path := [4, 1] }, .value "B"),
    ({ field := computedChoice.id, path := [4, 2] }, .noValue),
    ({ field := computedChoice.id, path := [5, 1] },
      .poison .declaredConstraint)]
  consumer := [
    ({ field := target.id, path := [1] }, .value "A"),
    ({ field := target.id, path := [2] }, .value "B"),
    ({ field := target.id, path := [3] }, .noValue),
    ({ field := target.id, path := [4] }, .poison .computedDependency),
    ({ field := target.id, path := [5] }, .poison .computedDependency)]
} := by
  native_decide

private def dependentNumberProducer? (sourceName := "ComputedChoice") :
    Option (CheckedAddressedFieldValueAsNumber model) :=
  (checkAddressedFieldValueAsNumber model ["Form", "Rows", "Items"]
    computedGate.id (.category (bare sourceName) "Numeric")).toOption

private def serialPlan? :
    Option (CheckedAddressedEnumerationToNumberHavingCascade model) := do
  let enumerationProducer ← enumerationProducer?
  let numberProducer ← dependentNumberProducer?
  let consumer ← consumer? (source "ComputedChoice" (having "ComputedGate"))
  (checkAddressedEnumerationToNumberHavingCascade enumerationProducer
    numberProducer consumer).toOption

private def serialError?
    (enumerationProducer := enumerationProducer?)
    (numberProducer := dependentNumberProducer? "OtherChoice") :
    Option AddressedEnumerationToNumberHavingCascadeElabError := do
  let enumerationProducer ← enumerationProducer
  let numberProducer ← numberProducer
  let consumer ← consumer? (source "ComputedChoice" (having "ComputedGate"))
  match checkAddressedEnumerationToNumberHavingCascade enumerationProducer
      numberProducer consumer with
  | .ok _ => none
  | .error cause => some cause

private def serialRows : List RowAddr :=
  [1, 2, 3].flatMap fun index =>
    [row 10 [index], row 20 [index, 1]]

private def serialInput? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := serialRows
    cells := [
      numericCell limit [1] "1" 1,
      numericCell limit [2] "1" 1,
      numericCell limit [3] "1" 1,
      cell directChoice [3] "A" (.parsed (.enum "A")),
      cell target [2] "B" (.parsed (.enum "B")),
      cell target [3] "A" (.parsed (.enum "A")),
      cell rawChoice [1, 1] "A" (.parsed (.enum "A")),
      cell rawChoice [2, 1] "C" (.parsed (.enum "C")),
      cell rawChoice [3, 1] "C" (.parsed (.enum "C")),
      cell computedChoice [1, 1] "B" (.parsed (.enum "B")),
      cell computedChoice [2, 1] "A" (.parsed (.enum "A")),
      cell computedChoice [3, 1] "A" (.parsed (.enum "A")),
      numericCell computedGate [1, 1] "2" 2,
      numericCell computedGate [2, 1] "1" 1,
      numericCell computedGate [3, 1] "1" 1]
  }).toOption

private structure SerialSummary where
  analysis : AddressedEnumerationToNumberHavingCascadeAnalysis
  enumerationProducer : List (CellAddr × TokenComputationResult)
  numberProducer : List (CellAddr × NumericDependencyObservation)
  consumer : List (CellAddr × TokenComputationResult)
  deriving Repr, DecidableEq

private def serialSummary? : Option SerialSummary := do
  let plan ← serialPlan?
  let input ← serialInput?
  let outcomes ← plan.execute input |>.toOption
  pure {
    analysis := plan.analyze
    enumerationProducer := outcomes.enumerationProducer.map fun item =>
      (item.targetField, item.result)
    numberProducer := outcomes.numberProducer.map fun item =>
      (item.targetField, item.outcome.dependencyObservation)
    consumer := outcomes.consumer.map fun item =>
      (item.targetField, item.result)
  }

/- The serial plan exposes both exact producer edges. Fresh Enumeration state reaches category conversion and the final selected value, reached poison crosses both boundaries cause-blind, and the direct prefix hides the completed poison. -/
example : serialPlan?.isSome = true ∧
    serialError? = some .missingEnumerationNumberDependency ∧
    serialError? (enumerationProducer := enumerationProducer?
      (absolute ["Form", "Rows"] "Target")) =
        some .enumerationProducerReadsConsumer ∧
    serialSummary? = some {
  analysis := {
    enumerationProducerTarget := computedChoice.id
    numberProjection := .category "Numeric"
    numberProducerTarget := computedGate.id
    consumerTarget := target.id
    fieldDependencies := [
      (computedChoice.id, [rawChoice.id]),
      (computedGate.id, [computedChoice.id]),
      (target.id, [directChoice.id, computedChoice.id, computedGate.id,
        limit.id])]
  }
  enumerationProducer := [
    ({ field := computedChoice.id, path := [1, 1] }, .value "A"),
    ({ field := computedChoice.id, path := [2, 1] },
      .poison .declaredConstraint),
    ({ field := computedChoice.id, path := [3, 1] },
      .poison .declaredConstraint)]
  numberProducer := [
    ({ field := computedGate.id, path := [1, 1] },
      .value { unscaled := 1, scale := 0 }),
    ({ field := computedGate.id, path := [2, 1] }, .poisoned),
    ({ field := computedGate.id, path := [3, 1] }, .poisoned)]
  consumer := [
    ({ field := target.id, path := [1] }, .value "A"),
    ({ field := target.id, path := [2] }, .poison .computedDependency),
    ({ field := target.id, path := [3] }, .value "A")]
} := by
  native_decide

private structure SerialResultApplicationSummary where
  enumerationProducerValues : List (CellAddr × String)
  enumerationProducerChanges : List (CellAddr × String)
  enumerationProducerCleared : List CellAddr
  enumerationProducerMessages : List Nat
  numberValues : List (CellAddr × StoredNumber)
  numberChanges : List (CellAddr × StoredNumber)
  numberCleared : List CellAddr
  consumerValues : List (CellAddr × String)
  consumerChanges : List (CellAddr × String)
  consumerCleared : List CellAddr
  consumerMessages : List Nat
  numberApplied : List (CellAddr × NumericTargetState)
  enumerationApplied : List (CellAddr × StringTargetState)
  deriving Repr, DecidableEq

private def serialResultDestination? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := serialRows, cells := [
    numericCell computedGate [1, 1] "8" 8,
    numericCell computedGate [2, 1] "8" 8,
    numericCell computedGate [3, 1] "8" 8,
    cell computedChoice [1, 1] "B" (.parsed (.enum "B")),
    cell computedChoice [2, 1] "B" (.parsed (.enum "B")),
    cell computedChoice [3, 1] "B" (.parsed (.enum "B")),
    cell target [1] "B" (.parsed (.enum "B")),
    cell target [2] "A" (.parsed (.enum "A")),
    cell target [3] "B" (.parsed (.enum "B"))] }).toOption

private def serialResultApplicationSummary? :
    Option SerialResultApplicationSummary := do
  let plan ← serialPlan?
  let input ← serialInput?
  let destination ← serialResultDestination?
  let view ← plan.executeResult input (fun _ => ()) [] [11] [22] |>.toOption
  let numberApplied ← view.number.applyToChecked destination |>.toOption
  let enumerationApplied ← view.applyEnumerationsToChecked destination |>.toOption
  let numberAddresses := [1, 2, 3].map fun outer =>
    ({ field := computedGate.id, path := [outer, 1] } : CellAddr)
  let enumerationAddresses := [
    ({ field := computedChoice.id, path := [1, 1] } : CellAddr),
    { field := computedChoice.id, path := [2, 1] },
    { field := computedChoice.id, path := [3, 1] },
    { field := target.id, path := [1] },
    { field := target.id, path := [2] },
    { field := target.id, path := [3] }]
  pure {
    enumerationProducerValues := view.enumerationProducer.withoutErrors.map
      fun item => (item.targetField, item.value.text)
    enumerationProducerChanges := view.enumerationProducer.withChanges.map
      fun item => (item.targetField, item.value.text)
    enumerationProducerCleared := view.enumerationProducer.cleared
    enumerationProducerMessages :=
      view.enumerationProducer.formalErrorsInOperands
    numberValues := view.number.withoutErrors.map fun item =>
      (item.targetField, item.value)
    numberChanges := view.number.withChanges.map fun item =>
      (item.targetField, item.value)
    numberCleared := view.number.cleared
    consumerValues := view.consumer.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    consumerChanges := view.consumer.withChanges.map fun item =>
      (item.targetField, item.value.text)
    consumerCleared := view.consumer.cleared
    consumerMessages := view.consumer.formalErrorsInOperands
    numberApplied := numberAddresses.map fun address =>
      (address, numberApplied.stateAt address)
    enumerationApplied := enumerationAddresses.map fun address =>
      (address, enumerationApplied address)
  }

/- The serial phases classify against the immutable source and apply separately to a different destination. The source-identical final success remains inert against a conflicting destination value. -/
example : serialResultApplicationSummary? = some {
  enumerationProducerValues := [
    ({ field := computedChoice.id, path := [1, 1] }, "A")]
  enumerationProducerChanges := [
    ({ field := computedChoice.id, path := [1, 1] }, "A")]
  enumerationProducerCleared := [
    { field := computedChoice.id, path := [2, 1] },
    { field := computedChoice.id, path := [3, 1] }]
  enumerationProducerMessages := [11]
  numberValues := [
    ({ field := computedGate.id, path := [1, 1] },
      { unscaled := 1, scale := 0 })]
  numberChanges := [
    ({ field := computedGate.id, path := [1, 1] },
      { unscaled := 1, scale := 0 })]
  numberCleared := [
    { field := computedGate.id, path := [2, 1] },
    { field := computedGate.id, path := [3, 1] }]
  consumerValues := [
    ({ field := target.id, path := [1] }, "A"),
    ({ field := target.id, path := [3] }, "A")]
  consumerChanges := [({ field := target.id, path := [1] }, "A")]
  consumerCleared := [{ field := target.id, path := [2] }]
  consumerMessages := [22]
  numberApplied := [
    ({ field := computedGate.id, path := [1, 1] },
      .presentValue (.decimal { unscaled := 1, scale := 0 })),
    ({ field := computedGate.id, path := [2, 1] }, .presentEmpty),
    ({ field := computedGate.id, path := [3, 1] }, .presentEmpty)]
  enumerationApplied := [
    ({ field := computedChoice.id, path := [1, 1] },
      .presentValue ⟨"A", by decide⟩),
    ({ field := computedChoice.id, path := [2, 1] }, .presentEmpty),
    ({ field := computedChoice.id, path := [3, 1] }, .presentEmpty),
    ({ field := target.id, path := [1] },
      .presentValue ⟨"A", by decide⟩),
    ({ field := target.id, path := [2] }, .presentEmpty),
    ({ field := target.id, path := [3] },
      .presentValue ⟨"B", by decide⟩)]
} := by
  native_decide

private structure ResultApplicationSummary where
  numberValues : List (CellAddr × StoredNumber)
  numberChanges : List (CellAddr × StoredNumber)
  numberCleared : List CellAddr
  producerValues : List (CellAddr × String)
  producerChanges : List (CellAddr × String)
  producerCleared : List CellAddr
  producerMessages : List Nat
  consumerValues : List (CellAddr × String)
  consumerChanges : List (CellAddr × String)
  consumerCleared : List CellAddr
  consumerMessages : List Nat
  numberApplied : List (CellAddr × NumericTargetState)
  enumerationApplied : List (CellAddr × StringTargetState)
  deriving Repr, DecidableEq

private def resultDestination? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells := [
    numericCell computedGate [1, 1] "8" 8,
    numericCell computedGate [2, 1] "8" 8,
    numericCell computedGate [3, 1] "8" 8,
    numericCell computedGate [4, 1] "8" 8,
    numericCell computedGate [4, 2] "8" 8,
    numericCell computedGate [5, 1] "8" 8,
    cell computedChoice [1, 1] "A" (.parsed (.enum "A")),
    cell computedChoice [2, 1] "A" (.parsed (.enum "A")),
    cell computedChoice [3, 1] "A" (.parsed (.enum "A")),
    cell computedChoice [4, 1] "A" (.parsed (.enum "A")),
    cell computedChoice [4, 2] "A" (.parsed (.enum "A")),
    cell computedChoice [5, 1] "A" (.parsed (.enum "A")),
    cell target [1] "B" (.parsed (.enum "B")),
    cell target [2] "A" (.parsed (.enum "A")),
    cell target [3] "A" (.parsed (.enum "A")),
    cell target [4] "A" (.parsed (.enum "A")),
    cell target [5] "B" (.parsed (.enum "B"))] }).toOption

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let plan ← plan?
  let input ← input?
  let destination ← resultDestination?
  let view ← plan.executeResult input (fun _ => ()) [] [11] [22]
    |>.toOption
  let numberApplied ← view.number.applyToChecked destination |>.toOption
  let enumerationApplied ← view.applyEnumerationsToChecked destination |>.toOption
  let numberAddresses := [[1, 1], [2, 1], [5, 1]]
    |>.map fun path => ({ field := computedGate.id, path } : CellAddr)
  let enumerationAddresses := [
    ({ field := computedChoice.id, path := [2, 1] } : CellAddr),
    { field := computedChoice.id, path := [4, 1] },
    { field := computedChoice.id, path := [4, 2] },
    { field := target.id, path := [1] }, { field := target.id, path := [2] },
    { field := target.id, path := [3] }]
  pure {
    numberValues := view.number.withoutErrors.map fun item =>
      (item.targetField, item.value)
    numberChanges := view.number.withChanges.map fun item =>
      (item.targetField, item.value)
    numberCleared := view.number.cleared
    producerValues := view.enumerationProducer.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    producerChanges := view.enumerationProducer.withChanges.map fun item =>
      (item.targetField, item.value.text)
    producerCleared := view.enumerationProducer.cleared
    producerMessages := view.enumerationProducer.formalErrorsInOperands
    consumerValues := view.consumer.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    consumerChanges := view.consumer.withChanges.map fun item =>
      (item.targetField, item.value.text)
    consumerCleared := view.consumer.cleared
    consumerMessages := view.consumer.formalErrorsInOperands
    numberApplied := numberAddresses.map fun address =>
      (address, numberApplied.stateAt address)
    enumerationApplied := enumerationAddresses.map fun address =>
      (address, enumerationApplied address)
  }

/- The three sourced phases classify independently; Number applies alone, while both Enumeration phases fold without destination-relative reclassification. -/
example : resultApplicationSummary? = some {
  numberValues := [
    ({ field := computedGate.id, path := [2, 1] },
      { unscaled := 2, scale := 0 }),
    ({ field := computedGate.id, path := [3, 1] },
      { unscaled := 1, scale := 0 }),
    ({ field := computedGate.id, path := [4, 2] },
      { unscaled := 0, scale := 0 }),
    ({ field := computedGate.id, path := [5, 1] },
      { unscaled := 1, scale := 0 })]
  numberChanges := [
    ({ field := computedGate.id, path := [2, 1] },
      { unscaled := 2, scale := 0 }),
    ({ field := computedGate.id, path := [3, 1] },
      { unscaled := 1, scale := 0 })]
  numberCleared := [
    { field := computedGate.id, path := [1, 1] },
    { field := computedGate.id, path := [4, 1] }]
  producerValues := [
    ({ field := computedChoice.id, path := [2, 1] }, "B"),
    ({ field := computedChoice.id, path := [4, 1] }, "B")]
  producerChanges := [
    ({ field := computedChoice.id, path := [2, 1] }, "B")]
  producerCleared := [
    { field := computedChoice.id, path := [1, 1] },
    { field := computedChoice.id, path := [3, 1] },
    { field := computedChoice.id, path := [4, 2] },
    { field := computedChoice.id, path := [5, 1] }]
  producerMessages := [11]
  consumerValues := [
    ({ field := target.id, path := [1] }, "A"),
    ({ field := target.id, path := [2] }, "B")]
  consumerChanges := [({ field := target.id, path := [2] }, "B")]
  consumerCleared := [
    { field := target.id, path := [3] },
    { field := target.id, path := [4] }]
  consumerMessages := [22]
  numberApplied := [
    ({ field := computedGate.id, path := [1, 1] }, .presentEmpty),
    ({ field := computedGate.id, path := [2, 1] },
      .presentValue (.decimal { unscaled := 2, scale := 0 })),
    ({ field := computedGate.id, path := [5, 1] },
      .presentValue (.decimal { unscaled := 8, scale := 0 }))]
  enumerationApplied := [
    ({ field := computedChoice.id, path := [2, 1] },
      .presentValue ⟨"B", by decide⟩),
    ({ field := computedChoice.id, path := [4, 1] },
      .presentValue ⟨"A", by decide⟩),
    ({ field := computedChoice.id, path := [4, 2] }, .presentEmpty),
    ({ field := target.id, path := [1] }, .presentValue ⟨"B", by decide⟩),
    ({ field := target.id, path := [2] }, .presentValue ⟨"B", by decide⟩),
    ({ field := target.id, path := [3] }, .presentEmpty)]
} := by
  native_decide

end A12Kernel.Conformance.AddressedEnumerationNumberHavingJoin
