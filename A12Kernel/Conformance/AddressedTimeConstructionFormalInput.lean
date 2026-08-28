import A12Kernel.Elaboration.AddressedTimeConstructionFormalInput

/-! # Addressed `Time(...)` direct-field formal-input locks -/

namespace A12Kernel.Conformance.AddressedTimeConstructionFormalInput

open A12Kernel

private def numberField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (maximum : Rat) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := { maximum := some maximum }
}

private def rootHour := numberField 1 "RootHour" ["Order"] [] 23
private def projectMinute :=
  numberField 2 "ProjectMinute" ["Order", "Projects"] [10] 59
private def rowSecond :=
  numberField 3 "RowSecond" ["Order", "Projects", "Tasks"] [10, 20] 59
private def target : FlatFieldDecl := {
  id := 4
  name := "SelectedTime"
  groupPath := ["Order", "Projects", "Tasks"]
  repeatableScope := [10, 20]
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" }
}
private def unrelated := numberField 5 "Unrelated" ["Order"] [] 99

private def model : FlatModel := {
  fields := [rootHour, projectMinute, rowSecond, target, unrelated]
  repeatableGroups := [
    { level := 10, path := ["Order", "Projects"], repeatability := some 2 },
    { level := 20, path := ["Order", "Projects", "Tasks"],
      repeatability := some 2 }
  ]
}

private def absolute (groups : GroupPath) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def operation? :=
  (checkAddressedTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id
    (.second
      (.number (absolute ["Order"] rootHour.name))
      (.number (absolute ["Order", "Projects"] projectMinute.name))
      (.number (absolute ["Order", "Projects", "Tasks"] rowSecond.name))))
    |>.toOption

private def row (group : RepeatableLevel) (path : List Nat) : RowAddr :=
  { group, path }

private def rejected (field : FieldId) (path : List Nat)
    (cause : BaseFormalCause) : ClassifiedCellInput := {
  address := { field, path }
  stored := match cause with
    | .declaredConstraint => "60"
    | _ => "bad"
  raw := .rejected cause
}

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [row 10 [1], row 20 [1, 1]]
    cells := [
      rejected target.id [1, 1] .malformed,
      rejected unrelated.id [] .malformed,
      rejected rootHour.id [] .declaredConstraint,
      rejected projectMinute.id [1] .declaredConstraint,
      rejected rowSecond.id [1, 1] .declaredConstraint
    ]
  }).toOption

/- The checked Time result inventories each direct component at its own exact scope while excluding the computed target and unrelated formal state. -/
example :
    (do
      let operation ← operation?
      let input ← input?
      let result ← operation.executeResultWithFormalInputs input |>.toOption
      let findings := result.time.formalErrorsInOperands
      pure (
        findings.length,
        [findings.contains {
            address := { field := rootHour.id, path := [] },
            cause := .declaredConstraint },
          findings.contains {
            address := { field := projectMinute.id, path := [1] },
            cause := .declaredConstraint },
          findings.contains {
            address := { field := rowSecond.id, path := [1, 1] },
            cause := .declaredConstraint },
          findings.any fun finding => finding.address.field == target.id,
          findings.any fun finding => finding.address.field == unrelated.id])) =
      some (3, [true, true, true, false, false]) := by
  native_decide

private def indexedHour :=
  numberField 11 "Hour" ["Clock", "Rows"] [30] 23

private def indexedTarget : FlatFieldDecl := {
  id := 12
  name := "SelectedTime"
  groupPath := ["Clock", "Rows"]
  repeatableScope := [30]
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" }
}

private def indexedModel : FlatModel := {
  fields := [indexedHour, indexedTarget]
  repeatableGroups := [{
    level := 30
    path := ["Clock", "Rows"]
    repeatability := some 2
    indexField := some indexedHour.id
  }]
}

private def indexedPrepared : PreparedFlatStringContext indexedModel
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler indexedModel).toOption.get (by native_decide)

private def indexedOperation? :
    Option (CheckedAddressedTimeConstructionComputation indexedModel) :=
  (checkAddressedTimeConstructionComputation indexedModel ["Clock", "Rows"]
    indexedTarget.id (.hour (.number
      (absolute ["Clock", "Rows"] indexedHour.name)))).toOption

private def indexedHourCell (row : Nat) : ClassifiedCellInput := {
  address := { field := indexedHour.id, path := [row] }
  stored := "5"
  raw := .parsed (.num 5)
}

private def indexedTargetCell (row : Nat) : ClassifiedCellInput := {
  address := { field := indexedTarget.id, path := [row] }
  stored := "01:00:00"
  raw := .parsed (.temporal (.time
    { epochMillis := 3600000 }
    ⟨1, 0, 0, by decide⟩))
}

private def indexedInput? : Option (CheckedDocument indexedModel) :=
  (checkDocument indexedPrepared "en_US" {
    instantiatedRows := [row 30 [1], row 30 [2]]
    cells := [
      indexedHourCell 1,
      indexedHourCell 2,
      indexedTargetCell 1,
      indexedTargetCell 2
    ]
  }).toOption

/- Duplicate numeric indexes are both eager formal inputs and reached hour-component poison, so both source-filled Time targets clear. -/
example :
    (do
      let operation ← indexedOperation?
      let input ← indexedInput?
      let result ← operation.executeResultWithFormalInputs input |>.toOption
      pure (
        result.time.formalErrorsInOperands,
        result.time.withoutErrors.map (·.targetField),
        result.time.withErrors,
        result.time.cleared)) = some ([
          {
            address := { field := indexedHour.id, path := [1] }
            cause := .duplicateIndex
          },
          {
            address := { field := indexedHour.id, path := [2] }
            cause := .duplicateIndex
          }
        ], [], [], [
          { field := indexedTarget.id, path := [1] },
          { field := indexedTarget.id, path := [2] }
        ]) := by
  native_decide

end A12Kernel.Conformance.AddressedTimeConstructionFormalInput
