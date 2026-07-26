import A12Kernel.Elaboration.SemanticIndex

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

/- The deterministic Lean reference projection selects the last duplicate occurrence in document order, while semantic index excludes that same key and reports the invalid column on lookup. -/
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
    some ([[(20, 1)], [(20, 2)]], some [(20, 2)], .value (.num 2),
      .unknown .duplicateIndex, .unknown .duplicateIndex)) = true := by
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
  group := demand
  indexField := { id := 1, info := numberInfo }
  targetField := {
    id := 2
    info := { scale := 0, signed := false }
  }
  key := .literal 5
  modelWellFormed := by native_decide
  groupOwned := by native_decide
  indexDeclared := by native_decide
  indexOwned := by native_decide
  targetOwned := by native_decide
  keyOwned := by native_decide
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

/- Number columns remain usable by semantic index, but parallel ordering fails closed until declaration-owned normalized rendering exists. -/
example : (preliminaryFor numberParallelModel numberParallelData).bind
    (fun preliminary =>
      match preliminary.resolveParallelIndexJoin demand supply with
      | .error error => some error
      | .ok _ => none) =
    some (.unsupportedParallelNumberIndex
      ["Order", "Demand", "Department"]) := by
  native_decide

end A12Kernel.Conformance.CheckedIndexColumn
