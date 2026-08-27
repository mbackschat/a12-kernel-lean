import A12Kernel.Elaboration.CurrentRepetitionAlternatingEnumerationHaving

/-! # Four-stage CurrentRepetition Number/String/Number/Enumeration locks -/

namespace A12Kernel.Conformance.CurrentRepetitionAlternatingEnumerationHaving

open A12Kernel

private def numberField (id : FieldId) (name : String)
    (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath := path, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := false } }
}

private def enumerationField (id : FieldId) (name : String)
    (path : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath := path, repeatableScope := scope
  policy := { kind := .enumeration }
  enumeration := some { storedTokens := ["A", "B"] }
}

private def base := numberField 1 "Base" ["Shipment", "Rows", "Lines"] [10, 20]
private def first := numberField 2 "FirstNumber" ["Shipment", "Rows", "Lines"] [10, 20]
private def second : FlatFieldDecl := {
  id := 3, name := "SecondString"
  groupPath := ["Shipment", "Rows", "Lines"]
  repeatableScope := [10, 20], policy := { kind := .string }
  stringPolicy := { maxLength := some 1 }
  stringPatternSource := some asciiDigitsPatternSource
}
private def third := numberField 4 "ThirdNumber" ["Shipment", "Rows", "Lines"] [10, 20]
private def target := enumerationField 5 "Target" ["Shipment", "Rows"] [10]
private def directChoice := enumerationField 6 "DirectChoice" ["Shipment", "Rows"] [10]
private def choice := enumerationField 7 "Choice" ["Shipment", "Rows", "Lines"] [10, 20]
private def limit := numberField 8 "Limit" ["Shipment", "Rows"] [10]

private def rows : RepeatableGroupDecl := {
  level := 10, path := ["Shipment", "Rows"], repeatability := some 1
}

private def lines : RepeatableGroupDecl := {
  level := 20, path := ["Shipment", "Rows", "Lines"], repeatability := some 2
}

private def model : FlatModel := {
  fields := [base, first, second, third, target, directChoice, choice, limit]
  repeatableGroups := [rows, lines]
}

private def bare (field : String) : SurfaceFieldPath := {
  base := .relative 0, groups := [], field
}

private def group : SurfaceGroupPath := {
  base := .absolute, groups := ["Shipment", "Rows", "Lines"]
}

private def numberRef (origin : HavingOrigin) (groups : List String)
    (field : String) : SurfaceHavingNumberRef := {
  origin, field := { base := .absolute, groups, field }
}

private def having (inner : String) : SurfaceCorrelatedHaving :=
  .compareNumbers .equal
    (numberRef .inner ["Shipment", "Rows", "Lines"] inner)
    (numberRef .outer ["Shipment", "Rows"] "Limit")

private def choiceStar (filter : SurfaceCorrelatedHaving) :
    SurfaceEnumerationFirstFilledOperand :=
  .star {
    base := .absolute
    groups := [{ name := "Shipment" }, { name := "Rows" },
      { name := "Lines", starred := true }]
    field := "Choice"
  } .stored (some filter)

private def serialHaving : SurfaceCorrelatedHaving :=
  .and (having "ThirdNumber") (having "FirstNumber")

private def source (filter : SurfaceCorrelatedHaving) :
    SurfaceEnumerationFirstFilledSource := {
  first := .field (.direct (bare "DirectChoice"))
  rest := [choiceStar filter]
}

private def prefix? : Option (CheckedCurrentRepetitionAlternatingChain model) :=
  (checkCurrentRepetitionAlternatingChain model lines.path group
    first.id (bare "Base") second.id (bare "FirstNumber")
    third.id (.direct (bare "SecondString"))).toOption

private def consumer? (authored := source serialHaving) :
    Option (CheckedAddressedEnumerationFirstFilledComputation model) :=
  (checkAddressedEnumerationFirstFilledComputation model ["Shipment", "Rows"]
    target.id authored).toOption

private def plan? :
    Option (CheckedCurrentRepetitionAlternatingEnumerationHaving model) := do
  let chain ← prefix?
  let consumer ← consumer?
  (checkCurrentRepetitionAlternatingEnumerationHaving chain consumer).toOption

private def planError? (authored : SurfaceEnumerationFirstFilledSource) :
    Option CurrentRepetitionAlternatingEnumerationHavingElabError := do
  let chain ← prefix?
  let consumer ← consumer? authored
  match checkCurrentRepetitionAlternatingEnumerationHaving chain consumer with
  | .ok _ => none
  | .error cause => some cause

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def numericCell (field : FlatFieldDecl) (path : List Nat) (value : Int) :
    ClassifiedCellInput := {
  address := { field := field.id, path }, stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def cell (field : FlatFieldDecl) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput := {
  address := { field := field.id, path }, stored, raw
}

private def storedString (text : String) (nonempty : text ≠ "") : StoredString :=
  { text, nonempty }

private def input? (poisoned : Bool) (direct : Option String := none) :
    Option (CheckedDocument model) :=
  let rows := if poisoned then [1] else [1, 2]
  let bases := if poisoned then [12] else [1, 2]
  let repeated := (rows.zip bases).flatMap fun (row, value) => [
    numericCell base [1, row] value,
    numericCell first [1, row] 9,
    cell second [1, row] (if row == 1 then "2" else "1")
      (.parsed (.str (if row == 1 then "2" else "1"))),
    numericCell third [1, row] (if row == 1 then 2 else 1),
    cell choice [1, row] (if row == 1 then "A" else "B")
      (.parsed (.enum (if row == 1 then "A" else "B")))]
  let directCell := direct.toList.map fun token =>
    cell directChoice [1] token (.parsed (.enum token))
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }] ++
      rows.map fun row => { group := 20, path := [1, row] }
    cells := [numericCell limit [1] 1] ++ directCell ++ repeated
  }).toOption

private structure Summary where
  analysis : CurrentRepetitionAlternatingEnumerationHavingAnalysis
  first : List (CellAddr × NumericDependencyObservation)
  second : List (CellAddr × StringTargetOutcome)
  third : List (CellAddr × NumericDependencyObservation)
  consumer : List (CellAddr × TokenComputationResult)
  deriving Repr, DecidableEq

private def summary? (input : CheckedDocument model) : Option Summary := do
  let plan ← plan?
  let outcomes ← plan.execute prepared.patterns input |>.toOption
  pure {
    analysis := plan.analyze
    first := outcomes.chain.rows.map fun row =>
      (row.first.targetField, row.first.outcome.dependencyObservation)
    second := outcomes.chain.rows.map fun row =>
      (row.second.targetField, row.second.outcome)
    third := outcomes.chain.rows.map fun row =>
      (row.third.targetField, row.third.outcome.dependencyObservation)
    consumer := outcomes.consumer.map fun item => (item.targetField, item.result)
  }

/- The checked four-stage route exposes all edges and refuses a final filter that omits the third Number target. -/
example : plan?.isSome = true ∧
    planError? (source (having "FirstNumber")) =
      some (.missingFilterDependency third.id) ∧
    plan?.map CheckedCurrentRepetitionAlternatingEnumerationHaving.analyze = some {
      structuralGroup := lines.path
      scope := [10, 20]
      thirdProjection := .stored
      consumerTarget := target.id
      fieldDependencies := [
        (first.id, [base.id]), (second.id, [first.id]),
        (third.id, [second.id]),
        (target.id, [directChoice.id, choice.id, third.id, limit.id,
          first.id])]
    } := by
  native_decide

/- Fresh third-phase values replace reversed stale seeds before the final filter. -/
example : (do let input ← input? false; summary? input) = some {
  analysis := {
    structuralGroup := lines.path, scope := [10, 20], thirdProjection := .stored
    consumerTarget := target.id
    fieldDependencies := [
      (first.id, [base.id]), (second.id, [first.id]),
      (third.id, [second.id]),
      (target.id, [directChoice.id, choice.id, third.id, limit.id,
        first.id])]
  }
  first := [
    ({ field := first.id, path := [1, 1] }, .value { unscaled := 1, scale := 0 }),
    ({ field := first.id, path := [1, 2] }, .value { unscaled := 2, scale := 0 })]
  second := [
    ({ field := second.id, path := [1, 1] },
      .accepted (storedString "1" (by decide))),
    ({ field := second.id, path := [1, 2] },
      .accepted (storedString "2" (by decide)))]
  third := [
    ({ field := third.id, path := [1, 1] }, .value { unscaled := 1, scale := 0 }),
    ({ field := third.id, path := [1, 2] }, .value { unscaled := 2, scale := 0 })]
  consumer := [({ field := target.id, path := [1] }, .value "A")]
} := by
  native_decide

/- The reached third-phase poison crosses the final boundary cause-blind, while the direct prefix hides the same completed poison. -/
private structure PoisonSummary where
  reachedString : List (CellAddr × StringTargetOutcome)
  reachedThird : List (CellAddr × NumericDependencyObservation)
  reachedConsumer : List (CellAddr × TokenComputationResult)
  hiddenConsumer : List (CellAddr × TokenComputationResult)
  deriving Repr, DecidableEq

private def poisonSummary? : Option PoisonSummary := do
  let reachedInput ← input? true
  let hiddenInput ← input? true (some "B")
  let reached ← summary? reachedInput
  let hidden ← summary? hiddenInput
  pure {
    reachedString := reached.second
    reachedThird := reached.third
    reachedConsumer := reached.consumer
    hiddenConsumer := hidden.consumer
  }

example : poisonSummary? = some {
  reachedString := [({ field := second.id, path := [1, 1] },
      .errored (storedString "12" (by decide)) .tooLong)]
  reachedThird := [({ field := third.id, path := [1, 1] }, .poisoned)]
  reachedConsumer := [
    ({ field := target.id, path := [1] }, .poison .computedDependency)]
  hiddenConsumer := [({ field := target.id, path := [1] }, .value "B")]
} := by
  native_decide

end A12Kernel.Conformance.CurrentRepetitionAlternatingEnumerationHaving
