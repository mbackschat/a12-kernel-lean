import A12Kernel.Elaboration.BooleanConstantComputation
import A12Kernel.Elaboration.CheckedDocument

/-! # Fixed Boolean and Confirm constant computation locks -/

namespace A12Kernel.Conformance.BooleanConstantComputation

open A12Kernel

private def booleanTarget : FlatFieldDecl := {
  id := 1
  groupPath := ["Review"]
  name := "Approved"
  policy := { kind := .boolean }
}

private def confirmTarget : FlatFieldDecl := {
  id := 2
  groupPath := ["Review"]
  name := "Confirmed"
  policy := { kind := .confirm }
}

private def unrelated : FlatFieldDecl := {
  booleanTarget with id := 3, name := "Unrelated"
}

private def model : FlatModel := {
  fields := [booleanTarget, confirmTarget, unrelated]
}

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def booleanCell (field : FlatFieldDecl) (value : Bool) :
    ClassifiedCellInput := {
  address := { field := field.id, path := [] }
  stored := if value then "true" else "false"
  raw := .parsed (.bool value)
}

private def confirmCell : ClassifiedCellInput := {
  address := { field := confirmTarget.id, path := [] }
  stored := "true"
  raw := .parsed (.conf true)
}

private def document? (boolean : Option Bool) (confirm : Bool)
    (unrelatedValue : Bool := false) : Option (CheckedDocument model) :=
  checkDocument prepared "en_US" {
    instantiatedRows := []
    cells := (boolean.map (booleanCell booleanTarget)).toList ++
      (if confirm then [confirmCell] else []) ++
      [booleanCell unrelated unrelatedValue]
  } |>.toOption

private def checked? (target : FieldId) (value : Bool) :
    Option (CheckedBooleanConstantComputation model) :=
  (checkBooleanConstantComputation model ["Review"] target value).toOption

private def result? (target : FieldId) (value : Bool)
    (boolean : Option Bool) (confirm : Bool) :
    Option (BooleanConstantComputationRunView model) := do
  let input ← document? boolean confirm
  let operation ← checked? target value
  pure (operation.executeResult input)

private def appliedState? (target : FieldId) (value : Bool)
    (boolean : Option Bool) (confirm : Bool)
    (destinationBoolean : Option Bool) (destinationConfirm : Bool)
    (field : FieldId) : Option BooleanTargetState := do
  let result ← result? target value boolean confirm
  let destination ← document? destinationBoolean destinationConfirm true
  pure (result.applyToChecked destination field)

/- Every admitted constant retains its exact typed value, while Confirm False has no executable checked carrier. -/
example : (do
    let booleanTrue ← checked? booleanTarget.id true
    let booleanFalse ← checked? booleanTarget.id false
    let confirmTrue ← checked? confirmTarget.id true
    pure (booleanTrue.execute, booleanFalse.execute, confirmTrue.execute,
      (checked? confirmTarget.id false).isNone)) =
  some (.value true, .value false, .value true, true) := by
  native_decide

/- Boolean False and Confirm True compare against their typed immutable source values. Source-identical successes retain values but produce no actions against a conflicting destination. -/
example :
    (result? booleanTarget.id false (some false) true).map
        (·.withoutErrors) =
      some [{ targetField := booleanTarget.id, value := false }] ∧
    (result? booleanTarget.id false (some false) true).map
        (·.withChanges) = some [] ∧
    (result? booleanTarget.id false (some false) true).map
        (·.cleared) = some [] ∧
    appliedState? booleanTarget.id false (some false) true
        (some true) false booleanTarget.id = some (.presentValue true) ∧
    appliedState? booleanTarget.id false (some false) true
        (some true) false unrelated.id = some (.presentValue true) := by
  native_decide

/- Confirm source identity uses its typed `.conf true` cell rather than treating the value as malformed or changed. -/
example :
    (result? confirmTarget.id true (some false) true).map
        (·.withoutErrors) =
      some [{ targetField := confirmTarget.id, value := true }] ∧
    (result? confirmTarget.id true (some false) true).map
        (·.withChanges) = some [] ∧
    (result? confirmTarget.id true (some false) true).map
        (·.cleared) = some [] ∧
    appliedState? confirmTarget.id true (some false) true
        (some true) false confirmTarget.id = some .absent ∧
    appliedState? confirmTarget.id true (some false) true
        (some true) false unrelated.id = some (.presentValue true) := by
  native_decide

/- A different or absent immutable source target produces one exact changed action, which applies without disturbing an unrelated destination field. -/
example :
    (result? booleanTarget.id false (some true) false).map
        (·.withChanges) =
      some [{ targetField := booleanTarget.id, value := false }] ∧
    appliedState? booleanTarget.id false (some true) false
        (some true) false booleanTarget.id = some (.presentValue false) ∧
    appliedState? booleanTarget.id false (some true) false
        (some true) false unrelated.id = some (.presentValue true) ∧
    (result? booleanTarget.id false (some true) false).map
        (·.noErrorOccurred) = some true := by
  native_decide

/- An absent Confirm source target makes the successful True value a change and materializes it only at that destination target. -/
example :
    (result? confirmTarget.id true (some true) false).map
        (·.withChanges) =
      some [{ targetField := confirmTarget.id, value := true }] ∧
    appliedState? confirmTarget.id true (some true) false
        (some true) false confirmTarget.id = some (.presentValue true) ∧
    appliedState? confirmTarget.id true (some true) false
        (some true) false unrelated.id = some (.presentValue true) ∧
    (result? confirmTarget.id true (some true) false).map
        (·.noErrorOccurred) = some true := by
  native_decide

/- Both admitted target kinds keep the unavailable runtime error, clear, and operand-formal channels empty. -/
example :
    (result? booleanTarget.id false (some true) false).map
        (fun view => (view.withErrors, view.cleared,
          view.formalErrorsInOperands)) = some ([], [], []) ∧
    (result? confirmTarget.id true (some true) false).map
        (fun view => (view.withErrors, view.cleared,
          view.formalErrorsInOperands)) = some ([], [], []) := by
  native_decide

end A12Kernel.Conformance.BooleanConstantComputation
