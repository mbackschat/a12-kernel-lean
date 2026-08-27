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
private def computedChoice := enumerationField 4 "ComputedChoice" ["Form", "Rows", "Items"] [10, 20]
private def limit := numberField 5 "Limit" ["Form", "Rows"] [10]
private def rawGate := numberField 6 "RawGate" ["Form", "Rows", "Items"] [10, 20]
private def computedGate := numberField 7 "ComputedGate" ["Form", "Rows", "Items"] [10, 20]

private def model : FlatModel := {
  fields := [target, directChoice, rawChoice, computedChoice, limit, rawGate,
    computedGate]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 5 },
    { level := 20, path := ["Form", "Rows", "Items"], repeatability := some 1 }]
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

private def rows : List RowAddr :=
  [1, 2, 3, 4, 5].flatMap fun index =>
    [row 10 [index], row 20 [index, 1]]

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells := [
    cell directChoice [1] "A" (.parsed (.enum "A")),
    cell limit [1] "1" (.parsed (.num 1)), cell limit [2] "2" (.parsed (.num 2)),
    cell limit [3] "3" (.parsed (.num 3)), cell limit [4] "1" (.parsed (.num 1)),
    cell limit [5] "1" (.parsed (.num 1)),
    cell rawGate [1, 1] "bad" (.rejected .malformed),
    cell rawGate [2, 1] "2" (.parsed (.num 2)), cell rawGate [3, 1] "1" (.parsed (.num 1)),
    cell rawGate [4, 1] "bad" (.rejected .malformed), cell rawGate [5, 1] "1" (.parsed (.num 1)),
    cell computedGate [1, 1] "1" (.parsed (.num 1)), cell computedGate [2, 1] "1" (.parsed (.num 1)),
    cell computedGate [3, 1] "3" (.parsed (.num 3)), cell computedGate [4, 1] "1" (.parsed (.num 1)),
    cell computedGate [5, 1] "1" (.parsed (.num 1)),
    cell rawChoice [1, 1] "C" (.parsed (.enum "C")), cell rawChoice [2, 1] "B" (.parsed (.enum "B")),
    cell rawChoice [3, 1] "C" (.parsed (.enum "C")), cell rawChoice [4, 1] "B" (.parsed (.enum "B")),
    cell rawChoice [5, 1] "C" (.parsed (.enum "C")),
    cell computedChoice [1, 1] "B" (.parsed (.enum "B")),
    cell computedChoice [2, 1] "A" (.parsed (.enum "A")),
    cell computedChoice [3, 1] "A" (.parsed (.enum "A")),
    cell computedChoice [4, 1] "A" (.parsed (.enum "A")),
    cell computedChoice [5, 1] "A" (.parsed (.enum "A"))] }).toOption

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
    ({ field := computedGate.id, path := [5, 1] },
      .value { unscaled := 1, scale := 0 })]
  enumerationProducer := [
    ({ field := computedChoice.id, path := [1, 1] },
      .poison .declaredConstraint),
    ({ field := computedChoice.id, path := [2, 1] }, .value "B"),
    ({ field := computedChoice.id, path := [3, 1] },
      .poison .declaredConstraint),
    ({ field := computedChoice.id, path := [4, 1] }, .value "B"),
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

end A12Kernel.Conformance.AddressedEnumerationNumberHavingJoin
