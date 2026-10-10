import A12Kernel.Elaboration.SemanticIndex
import A12Kernel.Elaboration.PartialSemanticIndex

/-! # Checked index-column and bounded parallel-join locks -/

namespace A12Kernel.Conformance.CheckedIndexColumn

open A12Kernel

private def indexDecl (id : FieldId) (group : String)
    (scope : RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := ["Order", group]
  name := "Department"
  policy := { kind := .string }
  repeatableScope := [scope]
}

private def targetDecl (id : FieldId) (group : String)
    (scope : RepeatableLevel) : FlatFieldDecl := {
  id
  groupPath := ["Order", group]
  name := "Headcount"
  policy := { kind := .number { scale := 0, signed := false } }
  repeatableScope := [scope]
}

private def demand : RepeatableGroupDecl := {
  level := 10
  path := ["Order", "Demand"]
  repeatability := some 2
  indexField := some 1
}

private def supply : RepeatableGroupDecl := {
  level := 20
  path := ["Order", "Supply"]
  repeatability := some 2
  indexField := some 3
}

private def model : FlatModel := {
  fields := [
    indexDecl 1 "Demand" 10, targetDecl 2 "Demand" 10,
    indexDecl 3 "Supply" 20, targetDecl 4 "Supply" 20
  ]
  repeatableGroups := [demand, supply]
}

private def row (group coordinate : Nat) : RowAddr :=
  { group, path := [coordinate] }

private def cell (field coordinate : Nat) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path := [coordinate] }
  stored
  raw
}

private def data : DocumentData := {
  instantiatedRows := [
    row 10 1, row 10 2, row 10 3, row 20 1, row 20 2
  ]
  cells := [
    cell 1 1 "Sales" (.parsed (.str "Sales")),
    cell 2 1 "7" (.parsed (.num 7)),
    cell 1 2 "Eng" (.parsed (.str "Eng")),
    cell 2 2 "3" (.parsed (.num 3)),
    cell 1 3 "Zulu" (.parsed (.str "Zulu")),
    cell 2 3 "99" (.parsed (.num 99)),
    cell 3 1 "Sales" (.parsed (.str "Sales")),
    cell 4 1 "8" (.parsed (.num 8)),
    cell 3 2 "Ops" (.parsed (.str "Ops")),
    cell 4 2 "2" (.parsed (.num 2))
  ]
}

private def world : World := { now := { epochMillis := 0 } }

private def preliminaryFor (candidate : FlatModel) (source : DocumentData) :
    Option (CheckedIndexPreliminary candidate) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler candidate).toOption
  let checked ← (checkDocument prepared "en_US" source).toOption
  checked.applyFullIndexPreliminary.toOption

private def joinFor (source : DocumentData) :
    Option (CheckedIndexPreliminary model × ResolvedParallelIndexJoin) := do
  let preliminary ← preliminaryFor model source
  let join ←
    (preliminary.resolveParallelIndexJoin demand supply).toOption
  pure (preliminary, join)

/- The join is ordered by exact normalized text rather than physical row order, and absence is explicit rather than encoded as a nonphysical coordinate. -/
example : ((joinFor data).map (fun (_, join) =>
    join.rows.map fun row =>
      (row.key, row.left.environment, row.right.environment)) ==
    some [
      (.text "Eng", some [(10, 2)], none),
      (.text "Ops", none, some [(20, 2)]),
      (.text "Sales", some [(10, 1)], some [(20, 1)])
    ]) = true := by
  native_decide

/- Matched sides read their physical preliminary cells; an unmatched clean side reads empty. -/
example : (
    ((joinFor data).bind fun (preliminary, join) => do
      let eng ← join.rows.find? fun row => row.key == .text "Eng"
      let sales ← join.rows.find? fun row => row.key == .text "Sales"
      let engDemand ← (eng.left.readValidation preliminary 2).toOption
      let engSupply ← (eng.right.readValidation preliminary 4).toOption
      let salesSupply ← (sales.right.readValidation preliminary 4).toOption
      pure (engDemand, engSupply, salesSupply)) ==
    some (.value (.num 3), .empty, .value (.num 8))) = true := by
  native_decide

private def invalidSupplyData : DocumentData := {
  data with
    cells := data.cells.filter fun input =>
      input.address != { field := 3, path := [2] }
}

/- Column invalidity affects only an unmatched side: a matched row in that same column remains definite. -/
example : (
    ((joinFor invalidSupplyData).bind fun (preliminary, join) => do
      let eng ← join.rows.find? fun row => row.key == .text "Eng"
      let sales ← join.rows.find? fun row => row.key == .text "Sales"
      let engSupply ← (eng.right.readValidation preliminary 4).toOption
      let salesSupply ← (sales.right.readValidation preliminary 4).toOption
      pure (engSupply, salesSupply)) ==
    some (.unknown .required, .value (.num 8))) = true := by
  native_decide

private def duplicateSupplyData : DocumentData := {
  data with
    cells := data.cells.map fun input =>
      if input.address == { field := 3, path := [2] } then
        { input with stored := "Sales", raw := .parsed (.str "Sales") }
      else
        input
}

private def currentTarget (address : CellAddr) : Except CheckedDocumentError CheckedCell :=
  pure {
    rawPresent := true
    parsed := some (.num (if address.field != 4 then 99 else if address.path == [1] then 41 else 52))
    findings := [] }

private def currentColumn (source : DocumentData) : Option ResolvedSemanticIndexColumn := do
  let preliminary ← preliminaryFor model source
  let column ← (preliminary.resolveIndexColumn supply).toOption
  (column.toSemanticIndexColumnWith currentTarget 4).toOption

example : ((currentColumn data).map fun column =>
    [column.lookupValue .computation "Sales", column.lookupValue .computation "Ops",
      column.lookupValue .computation "Absent"]) =
    some [.value (.num 41), .value (.num 52), .empty] := by
  native_decide

example : ((currentColumn invalidSupplyData).map fun column =>
    [column.lookupValue .validation "Sales", column.lookupValue .computation "Sales",
      column.lookupValue .validation "Absent"]) =
    some [.value (.num 41), .poison .required, .unknown .required] := by
  native_decide

example : ((currentColumn duplicateSupplyData).map fun column =>
    [column.lookupValue .validation "Sales", column.lookupValue .computation "Sales"]) =
    some [.unknown .duplicateIndex, .poison .duplicateIndex] := by
  native_decide

private def replacedTargetLookup (target : CheckedCell) (phase : Phase) : Option CellObservation := do
  let preliminary ← preliminaryFor model data
  let column ← (preliminary.resolveIndexColumn supply).toOption
  let semantic ← (column.toSemanticIndexColumnWith (fun _ => pure target) 4).toOption
  pure (semantic.lookupValue phase "Sales")

example : [
    replacedTargetLookup { rawPresent := false, parsed := none, findings := [] } .computation,
    replacedTargetLookup { rawPresent := true, parsed := none, findings := [.computedDependency] }
      .computation,
    replacedTargetLookup { rawPresent := true, parsed := none, findings := [.computedDependency] }
      .validation] = [some .empty, some (.poison .computedDependency),
        some (.unknown .computedDependency)] := by
  native_decide

private def keyedModel : FlatModel := {
  model with fields := model.fields ++ [{
    id := 5, groupPath := ["Order"], name := "Key", policy := { kind := .string } }] }

private def wrongKeyedModel : FlatModel := {
  keyedModel with fields := keyedModel.fields.map fun declaration =>
    if declaration.id == 5 then { declaration with policy := { kind := .boolean } } else declaration }

example : wrongKeyedModel.validate.isOk = true := by native_decide

example : (elaborateSemanticIndexSource wrongKeyedModel ["Order"] {
      target := { base := .absolute, groups := ["Order", "Supply"], field := "Headcount" }
      key := .field { base := .absolute, groups := ["Order"], field := "Key" }
    }).isOk = false := by native_decide

private def currentKeyLookup (source : DocumentData) (key : CellObservation)
    (phase : Phase) : Option CellObservation := do
  let preliminary ← preliminaryFor keyedModel source
  let selector ← (elaborateSemanticIndexSource keyedModel ["Order"] {
    target := { base := .absolute, groups := ["Order", "Supply"], field := "Headcount" }
    key := .field { base := .absolute, groups := ["Order"], field := "Key" }
  }).toOption
  (selector.lookupPreliminaryValueWith preliminary currentTarget
    (fun declaration => if declaration.id == 5 then key else .unknown .malformed) phase).toOption

example : [currentKeyLookup data (.value (.str "Sales")) .computation,
    currentKeyLookup data (.value (.str "Ops")) .computation,
    currentKeyLookup data .empty .computation,
    currentKeyLookup data (.poison .computedDependency) .computation,
    currentKeyLookup invalidSupplyData (.value (.str "Sales")) .validation,
    currentKeyLookup invalidSupplyData (.value (.str "Sales")) .computation,
    currentKeyLookup invalidSupplyData .empty .computation] =
    [some (.value (.num 41)), some (.value (.num 52)), some .empty,
      some (.poison .computedDependency), some (.value (.num 41)),
      some (.poison .required), some (.poison .required)] := by
  native_decide

private def duplicateBothData : DocumentData := {
  data with
    cells := data.cells.map fun input =>
      if input.address == { field := 1, path := [2] } ||
          input.address == { field := 3, path := [2] } then
        { input with stored := "Sales", raw := .parsed (.str "Sales") }
      else
        input
}

/- Duplicate participants remain in the checked carrier but are unavailable to both selectors. The clean far side still supplies the join key, so the duplicated side is unmatched and reads the column's exact cause. -/
example : (
    ((joinFor duplicateSupplyData).bind fun (preliminary, join) => do
      let eng ← join.rows.find? fun row => row.key == .text "Eng"
      let sales ← join.rows.find? fun row => row.key == .text "Sales"
      let engSupply ← (eng.right.readValidation preliminary 4).toOption
      let salesSupply ← (sales.right.readValidation preliminary 4).toOption
      let column ← (preliminary.resolveIndexColumn supply).toOption
      let semantic ← (column.toSemanticIndexColumn preliminary 4).toOption
      pure (column.entries.map (·.environment), sales.right.environment,
        salesSupply, engSupply,
        semantic.lookupValue .validation "Sales")) ==
    some ([[(20, 1)], [(20, 2)]], none, .unknown .duplicateIndex,
      .unknown .duplicateIndex, .unknown .duplicateIndex)) = true := by
  native_decide

/- When both columns duplicate the same key, neither side contributes it to the union and no all-unmatched phantom join row is created. -/
example : ((joinFor duplicateBothData).map fun (_, join) =>
    join.rows.map (·.key)) = some [] := by
  native_decide

/- A field owned by the other side is a structural error even when this side is unmatched. -/
example : (joinFor data).bind (fun (preliminary, join) => do
    let eng ← join.rows.find? fun row => row.key == .text "Eng"
    match eng.right.readValidation preliminary 2 with
    | .error error => some error
    | .ok _ => none) =
      some (.fieldOutsideGroup 2 ["Order", "Supply"]) := by
  native_decide

private def numberInfo : NumField := { scale := 2, signed := false }

private def numberIndexDecl (id : FieldId) (group : String)
    (scope : RepeatableLevel) : FlatFieldDecl :=
  { indexDecl id group scope with policy := { kind := .number numberInfo } }

private def numberModel : FlatModel := {
  model with fields := [
    numberIndexDecl 1 "Demand" 10, targetDecl 2 "Demand" 10,
    indexDecl 3 "Supply" 20, targetDecl 4 "Supply" 20
  ]
}

private def numberData (second : Rat) : DocumentData := {
  data with
    cells := data.cells.map fun input =>
      if input.address == { field := 1, path := [1] } then
        { input with stored := "5.00", raw := .parsed (.num 5) }
      else if input.address == { field := 1, path := [2] } then
        { input with stored := toString second, raw := .parsed (.num second) }
      else if input.address == { field := 1, path := [3] } then
        { input with stored := "6", raw := .parsed (.num 6) }
      else
        input
}

private def checkedNumber :
    CheckedNumberSemanticIndexSource numberModel := {
  toCheckedSemanticIndexSource := {
    group := demand
    indexDeclaration := numberIndexDecl 1 "Demand" 10
    targetDeclaration := targetDecl 2 "Demand" 10
    key := .literal (.number 5)
    modelWellFormed := by native_decide
    groupOwned := by native_decide
    indexDeclared := by native_decide
    indexOwned := by native_decide
    targetOwned := by native_decide
    keyOwned := by native_decide
    keyAgrees := by native_decide
  }
  singleGroup := by native_decide
  scalarKey := by native_decide
  indexNumber := by native_decide
  targetNumber := by native_decide
}

private def noKeyRaw : RawFlatContext := { read := fun _ => .empty }

/- The existing semantic-index owner now consumes the same checked column: Number spellings normalize to one duplicate key, while a clean normalized key selects its target. -/
example : (
    (preliminaryFor numberModel (numberData 5)).bind fun preliminary =>
      (checkedNumber.lookupPreliminaryValue
        preliminary noKeyRaw .validation).toOption,
    (preliminaryFor numberModel (numberData 6)).bind fun preliminary =>
      (checkedNumber.lookupPreliminaryValue
        preliminary noKeyRaw .validation).toOption) =
    (some (.unknown .duplicateIndex), some (.value (.num 7))) := by
  native_decide

private def numberParallelModel : FlatModel := {
  model with fields := [
    numberIndexDecl 1 "Demand" 10, targetDecl 2 "Demand" 10,
    numberIndexDecl 3 "Supply" 20, targetDecl 4 "Supply" 20
  ]
}

private def numberParallelData : DocumentData := {
  numberData 6 with
    cells := (numberData 6).cells.map fun input =>
      if input.address == { field := 3, path := [1] } then
        { input with stored := "5", raw := .parsed (.num 5) }
      else if input.address == { field := 3, path := [2] } then
        { input with stored := "6", raw := .parsed (.num 6) }
      else
        input
}

example : (preliminaryFor numberParallelModel numberParallelData).bind
    (fun preliminary => (preliminary.resolveParallelIndexJoin demand supply).toOption.map
      fun joined => joined.rows.map (·.key)) =
    some [.number 5, .number 6] := by
  native_decide

private def multilineModel : FlatModel := {
  keyedModel with fields := keyedModel.fields.map fun declaration =>
    if declaration.policy.kind == .string then
      { declaration with stringPolicy := { lineBreaksPermitted := true } }
    else declaration }

private def multilineData (left right : List String) (query : String) : DocumentData := {
  instantiatedRows := left.zipIdx.map (fun (_, index) => row 10 (index + 1)) ++
    right.zipIdx.map (fun (_, index) => row 20 (index + 1))
  cells := left.zipIdx.flatMap (fun (token, index) => [
      cell 1 (index + 1) token (.parsed (.str token)),
      cell 2 (index + 1) "7" (.parsed (.num 7))]) ++
    right.zipIdx.flatMap (fun (token, index) => [
      cell 3 (index + 1) token (.parsed (.str token)),
      cell 4 (index + 1) "8" (.parsed (.num 8))]) ++
    [{ address := { field := 5, path := [] }, stored := query, raw := .parsed (.str query) }] }

private def multilineSelector : Option (CheckedSemanticIndexSource multilineModel) :=
  (elaborateSemanticIndexSource multilineModel ["Order"] {
    target := { base := .absolute, groups := ["Order", "Supply"], field := "Headcount" }
    key := .field { base := .absolute, groups := ["Order"], field := "Key" } }).toOption

private def multilineLookup (keys : List String) (query : String) (phase : Phase) :
    Option (CellObservation × Option String × Option String) := do
  let preliminary ← preliminaryFor multilineModel (multilineData [] keys query)
  let selector ← multilineSelector
  let keyCell ← (preliminary.readAuthoredValidation { field := 5, path := [] }).toOption
  let key ← (selector.observeCurrentKey phase (fun _ => keyCell)
    (fun _ => preliminary.base.storedTextAt { field := 5, path := [] })).toOption
  let value ← (selector.lookupPreliminaryValueWith preliminary preliminary.readAuthoredValidation
    (fun _ => key) phase).toOption
  pure (value, preliminary.base.storedTextAt { field := 3, path := [1] },
    preliminary.base.storedTextAt { field := 5, path := [] })

example : [
    multilineLookup ["a\r\nb"] "a\nb" .computation,
    multilineLookup ["a\nb"] "a\r\nb" .computation,
    multilineLookup ["a\r\nb"] "a\r\nb" .validation,
    multilineLookup ["a\rb"] "a\nb" .computation,
    multilineLookup ["a\r\r\nb"] "a\r\nb" .computation,
    multilineLookup ["a\r\nb", "a\nb"] "a\nb" .validation,
    multilineLookup ["a\r\nb", "a\nb"] "a\r\nb" .computation] = [
      some (.value (.num 8), some "a\r\nb", some "a\nb"),
      some (.value (.num 8), some "a\nb", some "a\r\nb"),
      some (.value (.num 8), some "a\r\nb", some "a\r\nb"),
      some (.empty, some "a\rb", some "a\nb"),
      some (.empty, some "a\r\r\nb", some "a\r\nb"),
      some (.unknown .duplicateIndex, some "a\r\nb", some "a\nb"),
      some (.poison .duplicateIndex, some "a\r\nb", some "a\r\nb")] := by
  native_decide

private def multilineJoin (left right : String) :
    Option (List (String × SemanticIndexKey × Option Env × Option Env)) := do
  let preliminary ← preliminaryFor multilineModel (multilineData [left] [right] "a\nb")
  let joined ← (preliminary.resolveParallelIndexJoin demand supply).toOption
  pure (joined.rows.map fun row =>
    (row.iterationToken, row.key, row.left.environment, row.right.environment))

example : [("a\r\nb", "a\nb"), ("a\nb", "a\r\nb"), ("a\r\nb", "a\r\nb")].all
    (fun (left, right) => multilineJoin left right ==
      some [("a\nb", .text "a\nb", some [(10, 1)], some [(20, 1)])]) = true ∧
    (multilineJoin "a\rb" "a\nb" == some [
      ("a\nb", .text "a\nb", none, some [(20, 1)]),
      ("a\rb", .text "a\rb", some [(10, 1)], none)]) = true := by
  native_decide

private def currentMultilineKey (cell : CheckedCell) (phase : Phase) : Option CellObservation := do
  let selector ← multilineSelector
  (selector.observeCurrentKey phase (fun _ => cell) (fun _ => some "a\r\nb")).toOption

example : [
    currentMultilineKey { rawPresent := false, parsed := none, findings := [] } .computation,
    currentMultilineKey { rawPresent := true, parsed := none, findings := [.computedDependency] }
      .computation,
    currentMultilineKey { rawPresent := true, parsed := some (.str "a\nb"), findings := [.malformed] }
      .validation] = [some .empty, some (.poison .computedDependency), some (.unknown .malformed)] := by
  native_decide

private def changedPartialKeyLookup (indexRaw queryRaw : String) :
    Option (Option (CellObservation Env)) := do
  let preliminary ← preliminaryFor multilineModel (multilineData [] [indexRaw] "previous")
  let view ← (preliminary.base.applyPartialGeneratedPreliminary
    [RelevantEntityPattern.allInstances ["Order"]]).toOption
  let selector ← multilineSelector
  let changed := formalCheck { kind := .string } (.parsed (.str queryRaw))
  (selector.selectPartial view [] (fun _ _ => pure (some changed))).toOption

example : ["a\r\r\nb", "a\r\r\r\nb"].all (fun raw =>
    changedPartialKeyLookup raw raw == some (some (.value [(20, 1)]))) = true ∧
    (changedPartialKeyLookup "a\r\r\nb" "a\r\nb" == some (some .empty)) = true := by
  native_decide

end A12Kernel.Conformance.CheckedIndexColumn
