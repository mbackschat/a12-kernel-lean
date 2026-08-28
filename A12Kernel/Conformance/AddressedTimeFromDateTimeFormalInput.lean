import A12Kernel.Elaboration.AddressedTimeFromDateTimeFormalInput

/-! # Addressed `TimeFromDateTime` formal-input locks -/

namespace A12Kernel.Conformance.AddressedTimeFromDateTimeFormalInput

open A12Kernel

private def temporalField (id : FieldId) (name : String)
    (kind : TemporalKind) (components : TemporalComponents)
    (format : String) : FlatFieldDecl := {
  id, name
  groupPath := ["Schedule", "Slots"]
  repeatableScope := [10]
  policy := { kind := .temporal kind components }
  temporalTargetPolicy := some { format, partialMode := .full }
}

private def source := temporalField 1 "SlotStamp"
  .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss"
private def target := temporalField 2 "SlotTime"
  .time TemporalComponents.time "HH:mm:ss"
private def unrelated := temporalField 3 "Unrelated"
  .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss"

private def model : FlatModel := {
  fields := [source, target, unrelated]
  timeZoneId := "Europe/Berlin"
  repeatableGroups := [{
    level := 10
    path := ["Schedule", "Slots"]
    repeatability := some 2
    indexField := some source.id
  }]
}

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def bare (field : String) : SurfaceFieldPath :=
  { base := .relative 0, groups := [], field }

private def operation? : Option (CheckedAddressedTimeFromDateTime model) :=
  (checkAddressedTimeFromDateTime model ["Schedule", "Slots"] target.id
    (bare source.name)).toOption

private def sourceCell (row : Nat) : ClassifiedCellInput := {
  address := { field := source.id, path := [row] }
  stored := "2024-06-15T00:30:00"
  raw := .parsed (.temporal (.dateTime
    { epochMillis := 1718404200000 }
    { year := 2024, month := 6, day := 15 }
    ⟨0, 30, 0, by decide⟩ .storedGregorian))
}

private def targetCell (row : Nat) : ClassifiedCellInput := {
  address := { field := target.id, path := [row] }
  stored := "07:15:00"
  raw := .parsed (.temporal (.time { epochMillis := 0 }
    ⟨7, 15, 0, by decide⟩))
}

private def input? : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }
    ]
    cells := [sourceCell 1, sourceCell 2, targetCell 1, targetCell 2]
  }).toOption

private def finding (row : Nat) : ComputationFormalInputFinding := {
  address := { field := source.id, path := [row] }
  cause := .duplicateIndex
}

private structure Summary where
  operands : List FieldId
  targets : List FieldId
  selected : List FieldId
  findings : List ComputationFormalInputFinding
  values : List CellAddr
  errorsEmpty : Bool
  cleared : List CellAddr
  deriving Repr, DecidableEq

private def summary? : Option Summary := do
  let operation ← operation?
  let input ← input?
  let plan ← operation.formalInputPlan.toOption
  let result ← operation.executeResultWithFormalInputs input |>.toOption
  pure {
    operands := plan.operandFields
    targets := plan.computedFields
    selected := plan.selectedFields
    findings := result.time.formalErrorsInOperands
    values := result.time.withoutErrors.map (·.targetField)
    errorsEmpty := result.time.withErrors.isEmpty
    cleared := result.time.cleared
  }

/- The selected DateTime source remains the sole formal input, while duplicate index poison is both eagerly retained and reached by each source-filled Time target. -/
example : summary? = some {
    operands := [source.id]
    targets := [target.id]
    selected := [source.id]
    findings := [finding 1, finding 2]
    values := []
    errorsEmpty := true
    cleared := [
      { field := target.id, path := [1] },
      { field := target.id, path := [2] }
    ]
  } := by
  native_decide

end A12Kernel.Conformance.AddressedTimeFromDateTimeFormalInput
