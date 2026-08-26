import A12Kernel.Elaboration.AddressedEnumerationFirstFilledJoin

/-! # Two-producer Enumeration `FirstFilledValue` join locks -/

namespace A12Kernel.Conformance.AddressedEnumerationFirstFilledJoin

open A12Kernel

private def domain : EnumerationDeclaration := {
  storedTokens := ["A", "B"]
  categories := [{ name := "Choice", tokens := ["B", "A"] }]
}

private def enumerationField (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name
  groupPath := ["Form", "Rows"]
  repeatableScope := [10]
  policy := { kind := .enumeration }
  enumeration := some domain
}

private def sourceA := enumerationField 1 "SourceA"
private def sourceB := enumerationField 2 "SourceB"
private def producedA := enumerationField 3 "ProducedA"
private def producedB := enumerationField 4 "ProducedB"
private def target := enumerationField 5 "Target"
private def unrelated := enumerationField 6 "Unrelated"

private def model : FlatModel := {
  fields := [sourceA, sourceB, producedA, producedB, target, unrelated]
  repeatableGroups := [{
    level := 10, path := ["Form", "Rows"], repeatability := some 4
  }]
}

private def bare (name : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field := name }

private def producer? (destination source : FlatFieldDecl) :
    Option (CheckedAddressedEnumerationComputation model) :=
  (checkAddressedEnumerationComputation model ["Form", "Rows"] destination.id
    (.field (.direct (bare source.name)))).toOption

private def firstFilledSource (first second : FlatFieldDecl) :
    SurfaceEnumerationFirstFilledSource := {
  first := .field (.direct (bare first.name))
  rest := [.field (.category (bare second.name) "Choice")]
}

private def consumer? (first second : FlatFieldDecl) :
    Option (CheckedAddressedEnumerationFirstFilledComputation model) :=
  (checkAddressedEnumerationFirstFilledComputation model ["Form", "Rows"]
    target.id (firstFilledSource first second)).toOption

private def join? : Option (CheckedAddressedEnumerationFirstFilledJoin model) := do
  let first ← producer? producedA sourceA
  let second ← producer? producedB sourceB
  let consumer ← consumer? producedA producedB
  (certifyAddressedEnumerationFirstFilledJoin first second consumer).toOption

private def planError?
    (first? second? : Option (CheckedAddressedEnumerationComputation model))
    (consumer? : Option (CheckedAddressedEnumerationFirstFilledComputation model)) :
    Option AddressedEnumerationFirstFilledJoinPlanError := do
  let first ← first?
  let second ← second?
  let consumer ← consumer?
  match certifyAddressedEnumerationFirstFilledJoin first second consumer with
  | .ok _ => none
  | .error cause => some cause

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def address (field : FieldId) (row : Nat) : CellAddr :=
  { field, path := [row] }

private def cell (field : FlatFieldDecl) (row : Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput := {
  address := address field.id row, stored, raw
}

private def rows : List RowAddr := [
  { group := 10, path := [1] },
  { group := 10, path := [2] },
  { group := 10, path := [3] },
  { group := 10, path := [4] }]

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells := [
      cell sourceA 1 "A" (.parsed (.enum "A")),
      cell sourceB 1 "C" (.parsed (.enum "C")),
      cell sourceB 2 "A" (.parsed (.enum "A")),
      cell sourceB 3 "C" (.parsed (.enum "C")),
      cell producedA 1 "B" (.parsed (.enum "B")),
      cell producedA 2 "B" (.parsed (.enum "B")),
      cell producedB 1 "B" (.parsed (.enum "B")),
      cell producedB 2 "B" (.parsed (.enum "B")),
      cell producedB 3 "B" (.parsed (.enum "B")),
      cell target 1 "A" (.parsed (.enum "A")),
      cell target 2 "A" (.parsed (.enum "A")),
      cell target 3 "A" (.parsed (.enum "A"))]
  }).toOption

private structure JoinSummary where
  first : List (CellAddr × TokenComputationResult)
  second : List (CellAddr × TokenComputationResult)
  consumer : List (CellAddr × TokenComputationResult)
  deriving Repr, DecidableEq

private def summary? : Option JoinSummary := do
  let join ← join?
  let input ← input?
  let outcomes ← join.execute input |>.toOption
  pure {
    first := outcomes.firstProducer.map fun entry =>
      (entry.targetField, entry.result)
    second := outcomes.secondProducer.map fun entry =>
      (entry.targetField, entry.result)
    consumer := outcomes.consumer.map fun entry =>
      (entry.targetField, entry.result)
  }

private structure ResultSummary where
  firstChanges : List (CellAddr × String)
  firstCleared : List CellAddr
  secondChanges : List (CellAddr × String)
  secondCleared : List CellAddr
  consumerValues : List (CellAddr × String)
  consumerChanges : List (CellAddr × String)
  consumerCleared : List CellAddr
  deriving Repr, DecidableEq

private def resultSummary? : Option ResultSummary := do
  let join ← join?
  let input ← input?
  let view ← join.executeResult input
    ([] : List FormalCause) [] [] |>.toOption
  pure {
    firstChanges := view.firstProducer.withChanges.map fun entry =>
      (entry.targetField, entry.value.text)
    firstCleared := view.firstProducer.cleared
    secondChanges := view.secondProducer.withChanges.map fun entry =>
      (entry.targetField, entry.value.text)
    secondCleared := view.secondProducer.cleared
    consumerValues := view.consumer.withoutErrors.map fun entry =>
      (entry.targetField, entry.value.text)
    consumerChanges := view.consumer.withChanges.map fun entry =>
      (entry.targetField, entry.value.text)
    consumerCleared := view.consumer.cleared
  }

private structure ApplicationSummary where
  producedA1 : StringTargetState
  producedA2 : StringTargetState
  producedB1 : StringTargetState
  producedB2 : StringTargetState
  producedB3 : StringTargetState
  target1 : StringTargetState
  target2 : StringTargetState
  target3 : StringTargetState
  unrelated4 : StringTargetState
  deriving Repr, DecidableEq

private def applicationSummary? : Option ApplicationSummary := do
  let join ← join?
  let input ← input?
  let view ← join.executeResult input
    ([] : List FormalCause) [] [] |>.toOption
  let destination ← (checkDocument prepared "en_US" {
    instantiatedRows := rows
    cells := [
      cell producedA 1 "B" (.parsed (.enum "B")),
      cell producedA 2 "B" (.parsed (.enum "B")),
      cell producedB 1 "B" (.parsed (.enum "B")),
      cell producedB 2 "B" (.parsed (.enum "B")),
      cell producedB 3 "B" (.parsed (.enum "B")),
      cell target 1 "A" (.parsed (.enum "A")),
      cell target 2 "A" (.parsed (.enum "A")),
      cell target 3 "A" (.parsed (.enum "A")),
      cell unrelated 4 "B" (.parsed (.enum "B"))]
  }).toOption
  let applied ← view.applyToChecked destination |>.toOption
  pure {
    producedA1 := applied (address producedA.id 1)
    producedA2 := applied (address producedA.id 2)
    producedB1 := applied (address producedB.id 1)
    producedB2 := applied (address producedB.id 2)
    producedB3 := applied (address producedB.id 3)
    target1 := applied (address target.id 1)
    target2 := applied (address target.id 2)
    target3 := applied (address target.id 3)
    unrelated4 := applied (address unrelated.id 4)
  }

example : join?.isSome = true ∧
    planError? (producer? producedA sourceA) (producer? producedA sourceB)
      (consumer? producedA producedB) = some .producerTargetsSame ∧
    planError? (producer? producedA producedB) (producer? producedB sourceB)
      (consumer? producedA producedB) = some .firstProducerReadsSecond ∧
    planError? (producer? producedA sourceA) (producer? producedB producedA)
      (consumer? producedA producedB) = some .secondProducerReadsFirst ∧
    planError? (producer? producedA target) (producer? producedB sourceB)
      (consumer? producedA producedB) = some .firstProducerReadsConsumer ∧
    planError? (producer? producedA sourceA) (producer? producedB target)
      (consumer? producedA producedB) = some .secondProducerReadsConsumer ∧
    planError? (producer? producedA sourceA) (producer? producedB sourceB)
      (consumer? producedB producedA) = some .consumerSourcesMismatch := by
  native_decide

/- The first computed value stops the lazy scan before the second producer's poison; no-value reaches a category-projected value or poison, and double absence exhausts. Stale producer cells cannot leak into any branch. -/
example : summary? = some {
    first := [
      (address producedA.id 1, .value "A"),
      (address producedA.id 2, .noValue),
      (address producedA.id 3, .noValue),
      (address producedA.id 4, .noValue)]
    second := [
      (address producedB.id 1, .poison .declaredConstraint),
      (address producedB.id 2, .value "A"),
      (address producedB.id 3, .poison .declaredConstraint),
      (address producedB.id 4, .noValue)]
    consumer := [
      (address target.id 1, .value "A"),
      (address target.id 2, .value "B"),
      (address target.id 3, .poison .computedDependency),
      (address target.id 4, .noValue)]
  } := by
  native_decide

/- The three phases retain independent public result channels against immutable target state. -/
example : resultSummary? = some {
    firstChanges := [(address producedA.id 1, "A")]
    firstCleared := [address producedA.id 2]
    secondChanges := [(address producedB.id 2, "A")]
    secondCleared := [address producedB.id 1, address producedB.id 3]
    consumerValues := [
      (address target.id 1, "A"), (address target.id 2, "B")]
    consumerChanges := [(address target.id 2, "B")]
    consumerCleared := [address target.id 3]
  } := by
  native_decide

/- All retained actions fold in phase order onto a separate destination while an unrelated sentinel survives. -/
example : applicationSummary? = some {
    producedA1 := .presentValue ⟨"A", by decide⟩
    producedA2 := .presentEmpty
    producedB1 := .presentEmpty
    producedB2 := .presentValue ⟨"A", by decide⟩
    producedB3 := .presentEmpty
    target1 := .presentValue ⟨"A", by decide⟩
    target2 := .presentValue ⟨"B", by decide⟩
    target3 := .presentEmpty
    unrelated4 := .presentValue ⟨"B", by decide⟩
  } := by
  native_decide

end A12Kernel.Conformance.AddressedEnumerationFirstFilledJoin
