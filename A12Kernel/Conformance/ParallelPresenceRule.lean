import A12Kernel.Elaboration.ParallelPresenceRule

/-! # Bounded parallel presence-rule locks -/

namespace A12Kernel.Conformance.ParallelPresenceRule

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
  repeatability := some 3
  indexField := some 1
}

private def supply : RepeatableGroupDecl := {
  level := 20
  path := ["Order", "Supply"]
  repeatability := some 3
  indexField := some 3
}

private def model : FlatModel := {
  fields := [
    indexDecl 1 "Demand" 10, targetDecl 2 "Demand" 10,
    indexDecl 3 "Supply" 20, targetDecl 4 "Supply" 20,
    {
      id := 5
      groupPath := ["Order"]
      name := "Outside"
      policy := { kind := .string }
    }
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
    row 10 1, row 10 2, row 20 1, row 20 2
  ]
  cells := [
    cell 1 1 "Zulu" (.parsed (.str "Zulu")),
    cell 2 1 "7" (.parsed (.num 7)),
    cell 1 2 "Alpha" (.parsed (.str "Alpha")),
    cell 2 2 "3" (.parsed (.num 3)),
    cell 3 1 "Alpha" (.parsed (.str "Alpha")),
    cell 4 1 "8" (.parsed (.num 8)),
    cell 3 2 "Beta" (.parsed (.str "Beta")),
    cell 4 2 "2" (.parsed (.num 2))
  ]
}

private def invalidSupplyData : DocumentData := {
  data with
    instantiatedRows := data.instantiatedRows ++ [row 20 3]
    cells := data.cells ++ [cell 4 3 "4" (.parsed (.num 4))]
}

private def invalidDemandData : DocumentData := {
  data with
    instantiatedRows := data.instantiatedRows ++ [row 10 3]
    cells := data.cells ++ [cell 2 3 "4" (.parsed (.num 4))]
}

private def world : World := { now := { epochMillis := 0 } }

private def preliminaryFor (source : DocumentData) :
    Option (CheckedIndexPreliminary model) := do
  let prepared ←
    (prepareFlatStringContext
      world builtinStringPatternCompiler model).toOption
  let checked ← (checkDocument prepared "en_US" source).toOption
  checked.applyFullIndexPreliminary.toOption

private def messagePlan : MessageRenderPlan :=
  { parts := [.text "parallel"] }

private def checkedRule? (errorField : FieldId) :
    Option (CheckedParallelPresenceRule model) :=
  (checkParallelPresenceRule model 2 4 errorField "PI" .error
    messagePlan).toOption

/- Static construction requires the emitted error field to be one of the two positive operands. -/
example :
    (match checkParallelPresenceRule model 2 4 5 "PI" .error
        messagePlan with
      | .error error => some error
      | .ok _ => none) =
      some (.errorFieldNotOperand 5 2 4) := by
  native_decide

/- Two fields in one keyed group remain ordinary iteration; they cannot manufacture a parallel plan. -/
example :
    (match checkParallelPresenceRule model 1 2 2 "PI" .error
        messagePlan with
      | .error error => some error
      | .ok _ => none) =
      some (.join (.incompatibleGroups demand.path demand.path)) := by
  native_decide

private def evaluated? (errorField : FieldId) (source : DocumentData) :
    Option (List ParallelRuleRowOutcome) := do
  let preliminary ← preliminaryFor source
  let rule ← checkedRule? errorField
  (rule.evalFull preliminary).toOption

private def fired (field : FieldId) (path : List Nat) :
    FlatRuleOutcome :=
  .fired {
    errorAddress := { field, path }
    errorCode := "PI"
    severity := .error
    messageType := .value
    text := { text := "parallel" }
  }

/- The whole-rule scan follows lexical join-key order rather than either physical row order, and both clean unmatched directions remain ordinary nonfiring. -/
example : (evaluated? 2 data).map (·.map fun row => (row.key, row.outcome)) =
    some [
      (.text "Alpha", fired 2 [2]),
      (.text "Beta", .notFired),
      (.text "Zulu", .notFired)
    ] := by
  native_decide

/- The same condition can report on the other physical side without changing the join or condition order. -/
example : (evaluated? 4 data).map (·.map fun row => (row.key, row.outcome)) =
    some [
      (.text "Alpha", fired 4 [1]),
      (.text "Beta", .notFired),
      (.text "Zulu", .notFired)
    ] := by
  native_decide

/- A matched read stays definite in an invalid sibling column; only an unmatched read from that column is UNKNOWN. -/
example :
    (evaluated? 2 invalidSupplyData).map
      (·.map fun row => (row.key, row.outcome)) =
    some [
      (.text "Alpha", fired 2 [2]),
      (.text "Beta", .notFired),
      (.text "Zulu", .unknown)
    ] := by
  native_decide

/- Invalid-unmatched UNKNOWN is symmetric: it is not fabricated as an empty cell when the error target belongs to the clean side. -/
example :
    (evaluated? 4 invalidDemandData).map
      (·.map fun row => (row.key, row.outcome)) =
    some [
      (.text "Alpha", fired 4 [1]),
      (.text "Beta", .unknown),
      (.text "Zulu", .notFired)
    ] := by
  native_decide

/- A field outside both joined groups is structural misuse, never semantic UNKNOWN. -/
example : (preliminaryFor data).bind (fun preliminary =>
    (preliminary.resolveParallelIndexJoin demand supply).toOption.bind fun join =>
      join.rows.head?.bind fun first =>
        match first.readValidation preliminary 5 with
        | .error error => some error
        | .ok _ => none) =
    some (.fieldOutsideParallelGroups 5 demand.path supply.path) := by
  native_decide

end A12Kernel.Conformance.ParallelPresenceRule
