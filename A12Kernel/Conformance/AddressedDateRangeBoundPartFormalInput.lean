import A12Kernel.Elaboration.AddressedDateRangeBoundPartFormalInput

/-! # Addressed DateRange endpoint-component formal-input locks -/

namespace A12Kernel.Conformance.AddressedDateRangeBoundPartFormalInput

open A12Kernel

private def source : FlatFieldDecl := {
  id := 1
  name := "RowDates"
  groupPath := ["Order", "Rows"]
  repeatableScope := [10]
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }
}

private def target : FlatFieldDecl := {
  id := 2
  name := "Component"
  groupPath := ["Order", "Rows"]
  repeatableScope := [10]
  policy := { kind := .number { scale := 0, signed := false } }
}

private def model : FlatModel := {
  fields := [source, target]
  repeatableGroups := [{
    level := 10
    path := ["Order", "Rows"]
    repeatability := some 2
    indexField := some source.id
  }]
}

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def operation? :
    Option (CheckedAddressedDateRangeBoundPart model) :=
  (checkAddressedDateRangeBoundPart model ["Order", "Rows"] target.id
    { base := .relative 0, groups := [], field := source.name }
    .start .month).toOption

private def sourceCell (row : Nat) : ClassifiedCellInput := {
  address := { field := source.id, path := [row] }
  stored := "2024-06-01/2024-07-31"
  raw := (classifyStoredDateRangeForModel model.timeZoneId model.baseYear
    { format := "yyyy-MM-dd", separator := "/" }
    "2024-06-01/2024-07-31").toOption.get (by native_decide)
}

private def targetCell (row : Nat) : ClassifiedCellInput := {
  address := { field := target.id, path := [row] }
  stored := "99"
  raw := .parsed (.num 99)
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
  typedMessagesEmpty : Bool
  values : List CellAddr
  errors : List CellAddr
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
    findings := result.formalErrorsInOperands
    typedMessagesEmpty := result.numeric.formalErrorsInOperands.isEmpty
    values := result.numeric.withoutErrors.map (·.targetField)
    errors := result.numeric.withErrors.map (·.targetField)
    cleared := result.numeric.cleared
  }

/- The selected DateRange source remains the sole raw input. Duplicate-index poison reaches both rows while raw findings stay outside the typed Number message channel. -/
example : summary? = some {
    operands := [source.id]
    targets := [target.id]
    selected := [source.id]
    findings := [finding 1, finding 2]
    typedMessagesEmpty := true
    values := []
    errors := []
    cleared := [
      { field := target.id, path := [1] },
      { field := target.id, path := [2] }
    ]
  } := by
  native_decide

end A12Kernel.Conformance.AddressedDateRangeBoundPartFormalInput
