import A12Kernel.Elaboration.CurrentRepetitionAlternatingEnumerationHaving
import A12Kernel.Elaboration.NumericComputation.RunApplication

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
private def unrelated := numberField 9 "Unrelated" ["Shipment", "Rows"] [10]

private def rows : RepeatableGroupDecl := {
  level := 10, path := ["Shipment", "Rows"], repeatability := some 1
}

private def lines : RepeatableGroupDecl := {
  level := 20, path := ["Shipment", "Rows", "Lines"], repeatability := some 2
}

private def model : FlatModel := {
  fields := [base, first, second, third, target, directChoice, choice, limit,
    unrelated]
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

private def input? (poisoned : Bool) (direct : Option String := none)
    (targetValue : Option String := none) :
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
  let targetCell := targetValue.toList.map fun token =>
    cell target [1] token (.parsed (.enum token))
  (checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }] ++
      rows.map fun row => { group := 20, path := [1, row] }
    cells := [numericCell limit [1] 1] ++ directCell ++ targetCell ++ repeated
  }).toOption

private def formalInputDocument? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 20, path := [1, 1] },
      { group := 20, path := [1, 2] }]
    cells := [
      cell base [1, 1] "bad-base" (.rejected .malformed),
      cell directChoice [1] "bad-direct" (.rejected .declaredConstraint),
      cell choice [1, 2] "bad-choice" (.rejected .declaredConstraint),
      cell limit [1] "bad-limit" (.rejected .malformed),
      cell first [1, 1] "bad-first" (.rejected .malformed),
      cell second [1, 1] "bad-second" (.rejected .malformed),
      cell third [1, 1] "bad-third" (.rejected .malformed),
      cell target [1] "bad-target" (.rejected .declaredConstraint),
      cell unrelated [1] "bad-unrelated" (.rejected .malformed)]
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

private structure ResultApplicationSummary where
  numberChanges : List (CellAddr × StoredNumber)
  stringChanges : List (CellAddr × String)
  consumerChanges : List (CellAddr × String)
  numberFirstAtOne : NumericTargetState
  numberThirdAtTwo : NumericTargetState
  stringSecondAtOne : StringTargetState
  stringSecondAtTwo : StringTargetState
  consumerAtOne : StringTargetState
  directAtOne : StringTargetState
  chainResidual : List Nat
  consumerResidual : List Nat
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let plan ← plan?
  let input ← input? false
  let destination ← input? false (some "B") (some "B")
  let view ← plan.executeResult prepared.patterns input (fun _ => ()) []
    [11] [22] |>.toOption
  let numberApplied ← view.chain.number.applyToChecked destination |>.toOption
  let stringsApplied ← view.applyStringsToChecked destination |>.toOption
  pure {
    numberChanges := view.chain.number.withChanges.map fun item =>
      (item.targetField, item.value)
    stringChanges := view.chain.string.withChanges.map fun item =>
      (item.targetField, item.value.text)
    consumerChanges := view.consumer.withChanges.map fun item =>
      (item.targetField, item.value.text)
    numberFirstAtOne := numberApplied.stateAt { field := first.id, path := [1, 1] }
    numberThirdAtTwo := numberApplied.stateAt { field := third.id, path := [1, 2] }
    stringSecondAtOne := stringsApplied { field := second.id, path := [1, 1] }
    stringSecondAtTwo := stringsApplied { field := second.id, path := [1, 2] }
    consumerAtOne := stringsApplied { field := target.id, path := [1] }
    directAtOne := stringsApplied { field := directChoice.id, path := [1] }
    chainResidual := view.chain.string.formalErrorsInOperands
    consumerResidual := view.consumer.formalErrorsInOperands
  }

/- One execution projects all four phases against the immutable source and applies the family carriers independently to a conflicting destination. -/
example : resultApplicationSummary? = some {
  numberChanges := [
    ({ field := first.id, path := [1, 1] }, { unscaled := 1, scale := 0 }),
    ({ field := third.id, path := [1, 1] }, { unscaled := 1, scale := 0 }),
    ({ field := first.id, path := [1, 2] }, { unscaled := 2, scale := 0 }),
    ({ field := third.id, path := [1, 2] }, { unscaled := 2, scale := 0 })]
  stringChanges := [
    ({ field := second.id, path := [1, 1] }, "1"),
    ({ field := second.id, path := [1, 2] }, "2")]
  consumerChanges := [({ field := target.id, path := [1] }, "A")]
  numberFirstAtOne :=
    .presentValue (.decimal { unscaled := 1, scale := 0 })
  numberThirdAtTwo :=
    .presentValue (.decimal { unscaled := 2, scale := 0 })
  stringSecondAtOne := .presentValue (storedString "1" (by decide))
  stringSecondAtTwo := .presentValue (storedString "2" (by decide))
  consumerAtOne := .presentValue (storedString "A" (by decide))
  directAtOne := .presentValue (storedString "B" (by decide))
  chainResidual := [11]
  consumerResidual := [22]
} := by
  native_decide

/- The whole four-stage call inventories direct and filter inputs at their exact nested placements while excluding every computed target and the unrelated field. -/
example :
    (do
      let plan ← plan?
      let input ← formalInputDocument?
      let view ← plan.executeResultWithFormalInputs prepared.patterns input
        |>.toOption
      pure (view.formalErrorsInOperands,
        view.phases.chain.number.formalErrorsInOperands,
        view.phases.chain.string.formalErrorsInOperands,
        view.phases.consumer.formalErrorsInOperands)) = some ([
          { address := { field := base.id, path := [1, 1] }
            cause := .malformed },
          { address := { field := directChoice.id, path := [1] }
            cause := .declaredConstraint },
          { address := { field := choice.id, path := [1, 2] }
            cause := .declaredConstraint },
          { address := { field := limit.id, path := [1] }
            cause := .malformed }], [], [], []) := by
  native_decide

private structure PoisonResultApplicationSummary where
  numberChanges : List (CellAddr × StoredNumber)
  numberCleared : List CellAddr
  stringErrors : List (CellAddr × StringTargetError)
  consumerCleared : List CellAddr
  reachedFirst : NumericTargetState
  reachedSecond : StringTargetState
  reachedThird : NumericTargetState
  reachedConsumer : StringTargetState
  hiddenConsumerValues : List (CellAddr × String)
  hiddenConsumerChanges : List (CellAddr × String)
  hiddenConsumerCleared : List CellAddr
  hiddenConsumerAtDestination : StringTargetState
  deriving Repr, DecidableEq

private def poisonResultApplicationSummary? :
    Option PoisonResultApplicationSummary := do
  let plan ← plan?
  let reachedInput ← input? true none (some "A")
  let reached ← plan.executeResult prepared.patterns reachedInput
    (fun _ => ()) [] ([] : List Unit) [] |>.toOption
  let reachedNumber ← reached.chain.number.applyToChecked reachedInput |>.toOption
  let reachedStrings ← reached.applyStringsToChecked reachedInput |>.toOption
  let hiddenInput ← input? true (some "B") (some "B")
  let hiddenDestination ← input? true none (some "A")
  let hidden ← plan.executeResult prepared.patterns hiddenInput
    (fun _ => ()) [] ([] : List Unit) [] |>.toOption
  let hiddenStrings ← hidden.applyStringsToChecked hiddenDestination |>.toOption
  pure {
    numberChanges := reached.chain.number.withChanges.map fun item =>
      (item.targetField, item.value)
    numberCleared := reached.chain.number.cleared
    stringErrors := reached.chain.string.withErrors.map fun item =>
      (item.targetField, item.cause)
    consumerCleared := reached.consumer.cleared
    reachedFirst := reachedNumber.stateAt { field := first.id, path := [1, 1] }
    reachedSecond := reachedStrings { field := second.id, path := [1, 1] }
    reachedThird := reachedNumber.stateAt { field := third.id, path := [1, 1] }
    reachedConsumer := reachedStrings { field := target.id, path := [1] }
    hiddenConsumerValues := hidden.consumer.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    hiddenConsumerChanges := hidden.consumer.withChanges.map fun item =>
      (item.targetField, item.value.text)
    hiddenConsumerCleared := hidden.consumer.cleared
    hiddenConsumerAtDestination := hiddenStrings { field := target.id, path := [1] }
  }

/- Reached poison clears source-filled targets on application, while a source-identical direct result remains inert against a conflicting destination. -/
example : poisonResultApplicationSummary? = some {
  numberChanges := [
    ({ field := first.id, path := [1, 1] }, { unscaled := 12, scale := 0 })]
  numberCleared := [{ field := third.id, path := [1, 1] }]
  stringErrors := [({ field := second.id, path := [1, 1] }, .tooLong)]
  consumerCleared := [{ field := target.id, path := [1] }]
  reachedFirst := .presentValue (.decimal { unscaled := 12, scale := 0 })
  reachedSecond := .presentEmpty
  reachedThird := .presentEmpty
  reachedConsumer := .presentEmpty
  hiddenConsumerValues := [({ field := target.id, path := [1] }, "B")]
  hiddenConsumerChanges := []
  hiddenConsumerCleared := []
  hiddenConsumerAtDestination :=
    .presentValue (storedString "A" (by decide))
} := by
  native_decide

end A12Kernel.Conformance.CurrentRepetitionAlternatingEnumerationHaving
