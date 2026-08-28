import A12Kernel.Elaboration.GeneratedComputationFormalInput

/-! # Generated-table selected-preliminary execution locks -/

namespace A12Kernel.Conformance.GeneratedComputationValidation.PreparedExecution

open A12Kernel

private def selector : FlatFieldDecl := {
  id := 1
  groupPath := ["Form"]
  name := "Selector"
  policy := { kind := .number { scale := 0, signed := true } }
}

private def directSource : FlatFieldDecl := {
  id := 2
  groupPath := ["Form"]
  name := "DirectSource"
  policy := { kind := .number { scale := 0, signed := true } }
}

private def repeatedIndex : FlatFieldDecl := {
  id := 3
  groupPath := ["Form", "Rows"]
  name := "Index"
  repeatableScope := [10]
  policy := { kind := .number { scale := 0, signed := true } }
}

private def target : FlatFieldDecl := {
  id := 4
  groupPath := ["Form"]
  name := "Target"
  policy := { kind := .number { scale := 0, signed := true } }
}

private def model : FlatModel := {
  fields := [selector, directSource, repeatedIndex, target]
  repeatableGroups := [{
    level := 10
    path := repeatedIndex.groupPath
    repeatability := some 2
    indexField := some repeatedIndex.id
  }]
}

private def directOperation? :
    Option (CheckedNumericComputationOperation model) :=
  (elaborateNumericComputationOperation model ["Form"] target.id
    (.atom (.field {
      base := .absolute
      groups := directSource.groupPath
      field := directSource.name
    }))).toOption

private def repeatedIndexStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [
    { name := "Form" },
    { name := "Rows", starred := true }
  ]
  field := repeatedIndex.name
}

private def aggregateOperation? :
    Option (CheckedNumericComputationOperation model) :=
  (elaborateNumberEntityComputationOperation model ["Form"] target.id
    (.atom (.aggregate .sum {
      first := .star repeatedIndexStar
      rest := []
    }))).toOption

private def table? : Option (GeneratedComputationTable
    (CheckedNumericComputationOperation model)) := do
  let first ← directOperation?
  let second ← aggregateOperation?
  pure {
    targetField := target.id
    name := "preparedGeneratedTable"
    alternatives := .guarded {
      first := {
        precondition := .fieldFilled selector.id
        operation := first
      }
      second := {
        precondition := .fieldNotFilled selector.id
        operation := second
      }
    }
    messagePlan := { parts := [.text "generated mismatch"] }
  }

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def numberCell (field : FieldId) (path : List Nat)
    (value : Int) : ClassifiedCellInput := {
  address := { field, path }
  stored := toString value
  raw := .parsed (.num value)
  numericDecimal := some { unscaled := value, scale := 0 }
}

private def input? (selectFirst : Bool) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := [
      { group := 10, path := [1] },
      { group := 10, path := [2] }
    ]
    cells :=
      (if selectFirst then [numberCell selector.id [] 1] else []) ++ [
        numberCell directSource.id [] 7,
        numberCell repeatedIndex.id [1] 5,
        numberCell repeatedIndex.id [2] 5,
        numberCell target.id [] 9
      ]
  }).toOption

private def finding (row : Nat) : ComputationFormalInputFinding := {
  address := { field := repeatedIndex.id, path := [row] }
  cause := .duplicateIndex
}

private structure Summary where
  dependencies : List FieldId
  operands : List FieldId
  targets : List FieldId
  findings : List ComputationFormalInputFinding
  typedMessagesEmpty : Bool
  values : List (CellAddr × StoredNumber)
  changes : List (CellAddr × StoredNumber)
  errors : List CellAddr
  cleared : List CellAddr
  deriving Repr, DecidableEq

private def summary? (selectFirst : Bool) : Option Summary := do
  let table ← table?
  let input ← input? selectFirst
  let plan ← table.formalInputPlan.toOption
  let result ← (table.executeNumericResultWithFormalInputs
    { now := { epochMillis := 0 } } input).toOption
  pure {
    dependencies := table.fieldDependencies
    operands := plan.operandFields
    targets := plan.computedFields
    findings := result.formalErrorsInOperands
    typedMessagesEmpty := result.numeric.formalErrorsInOperands.isEmpty
    values := result.numeric.withoutErrors.map fun value =>
      (value.targetField, value.value)
    changes := result.numeric.withChanges.map fun value =>
      (value.targetField, value.value)
    errors := result.numeric.withErrors.map (·.targetField)
    cleared := result.numeric.cleared
  }

private def targetAddress : CellAddr := { field := target.id, path := [] }

private def seven : StoredNumber := { unscaled := 7, scale := 0 }

/- Eager duplicate findings from the later aggregate remain visible, but first-match selection hides their prepared poison and preserves the clean direct result. -/
example : summary? true = some {
    dependencies := [selector.id, directSource.id, repeatedIndex.id]
    operands := [selector.id, directSource.id, repeatedIndex.id]
    targets := [target.id]
    findings := [finding 1, finding 2]
    typedMessagesEmpty := true
    values := [(targetAddress, seven)]
    changes := [(targetAddress, seven)]
    errors := []
    cleared := []
  } := by
  native_decide

/- Selecting the aggregate reaches the same prepared duplicates as operation poison, clearing the stale target without copying eager findings into the typed message channel. -/
example : summary? false = some {
    dependencies := [selector.id, directSource.id, repeatedIndex.id]
    operands := [selector.id, directSource.id, repeatedIndex.id]
    targets := [target.id]
    findings := [finding 1, finding 2]
    typedMessagesEmpty := true
    values := []
    changes := []
    errors := []
    cleared := [targetAddress]
  } := by
  native_decide

end A12Kernel.Conformance.GeneratedComputationValidation.PreparedExecution
