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

private def crossGroupTarget : FlatFieldDecl := {
  id := 10
  groupPath := ["Store"]
  name := "Available"
  policy := { kind := .boolean }
}

private def rulesMarker : FlatFieldDecl := {
  id := 11
  groupPath := ["Rules"]
  name := "Marker"
  policy := { kind := .number { scale := 0, signed := false } }
}

private def crossGroupModel : FlatModel := {
  fields := [crossGroupTarget, rulesMarker]
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

private def crossGroupPrepared :
    PreparedFlatStringContext crossGroupModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler crossGroupModel).toOption.get (by native_decide)

private def crossGroupDocument? : Option (CheckedDocument crossGroupModel) :=
  checkDocument crossGroupPrepared "en_US" {
    instantiatedRows := []
    cells := []
  } |>.toOption

private def crossGroupChecked? :
    Option (CheckedBooleanConstantComputation crossGroupModel) :=
  (checkBooleanConstantComputation crossGroupModel ["Rules"]
    crossGroupTarget.id true).toOption

private def crossGroupResult? :
    Option (BooleanConstantComputationRunView crossGroupModel) := do
  let input ← crossGroupDocument?
  let operation ← crossGroupChecked?
  pure (operation.executeResult input)

private def crossGroupAppliedState? (field : FieldId) :
    Option BooleanTargetState := do
  let result ← crossGroupResult?
  let destination ← crossGroupDocument?
  pure (result.applyToChecked destination field)

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

/- A fixed constant runs at its target scope even when another fixed group owns the computation declaration. The empty checked document still has the target's implicit nonrepeatable instance. -/
example :
    crossGroupChecked?.isSome = true ∧
    crossGroupChecked?.map (fun operation =>
      (operation.declaringGroup, operation.target.groupPath)) =
        some (["Rules"], ["Store"]) ∧
    crossGroupResult?.map (·.withoutErrors) =
      some [{ targetField := crossGroupTarget.id, value := true }] ∧
    crossGroupResult?.map (·.withChanges) =
      some [{ targetField := crossGroupTarget.id, value := true }] ∧
    crossGroupAppliedState? crossGroupTarget.id =
      some (.presentValue true) ∧
    crossGroupAppliedState? rulesMarker.id = some .absent := by
  native_decide

/-! ## Repeatable constant targets

The Kernel admits a bare constant into a repeatable target from the target's own group and from any
ancestor of it, and computes one value per instantiated target row
([checkpoint](../../docs/SOURCES.md#src-cross-group-repeatable-constant-target)). -/

private def taskApproved : FlatFieldDecl := {
  id := 20
  groupPath := ["Probe", "Tasks"]
  name := "Approved"
  policy := { kind := .boolean }
  repeatableScope := [10]
}

private def taskConfirmed : FlatFieldDecl := {
  id := 21
  groupPath := ["Probe", "Tasks"]
  name := "Confirmed"
  policy := { kind := .confirm }
  repeatableScope := [10]
}

private def formLevel : FlatFieldDecl := {
  id := 22
  groupPath := ["Probe", "Store"]
  name := "Available"
  policy := { kind := .boolean }
}

private def repeatableModel : FlatModel := {
  fields := [taskApproved, taskConfirmed, formLevel]
  repeatableGroups := [
    { level := 10, path := ["Probe", "Tasks"], repeatability := some 3 }]
}

private def repeatablePrepared :
    PreparedFlatStringContext repeatableModel builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler repeatableModel).toOption.get (by native_decide)

private def taskRows (count : Nat) : Option (CheckedDocument repeatableModel) :=
  (checkDocument repeatablePrepared "en_US" {
    instantiatedRows :=
      (List.range count).map fun index => { group := 10, path := [index + 1] }
    cells := [] }).toOption

private def approvedAt (path : List Nat) : CellAddr :=
  { field := taskApproved.id, path }

/- Declaring the constant at the root computes once per instantiated target row, and at no row when
the group has none. The Kernel gives the identical outcomes from the target's own group, so the row
count comes from the target's scope and the declaring group contributes no repetition. -/
example : ((checkRepeatableBooleanConstantComputation
      repeatableModel ["Probe"] taskApproved.id true).toOption.bind fun operation => do
    let none? ← (taskRows 0).bind fun input => (operation.execute input).toOption
    let one ← (taskRows 1).bind fun input => (operation.execute input).toOption
    let three ← (taskRows 3).bind fun input => (operation.execute input).toOption
    pure (none?.map (·.targetField), one.map (·.targetField),
      three.map fun entry => (entry.targetField, entry.result))) =
    some ([], [approvedAt [1]],
      [(approvedAt [1], .value true), (approvedAt [2], .value true),
        (approvedAt [3], .value true)]) := by
  native_decide

/- Containment, not parenthood: the target's own group and every ancestor are admitted, and only a
group the target does not lie below is refused. The Kernel refuses that one
`MVK_ERROR_FIELD_NOT_IN_RULEGROUP` on this exact carrier. -/
example : ([["Probe", "Tasks"], ["Probe"]].map fun group =>
      (checkRepeatableBooleanConstantComputation
        repeatableModel group taskApproved.id true).toOption.isSome,
    match checkRepeatableBooleanConstantComputation
        repeatableModel ["Probe", "Store"] taskApproved.id true with
    | .error cause => cause.diagnostic?.map KernelStaticDiagnostic.kernelCode
    | .ok _ => none) =
    ([true, true], some "MVK_ERROR_FIELD_NOT_IN_RULEGROUP") := by
  native_decide

/- The Confirm asymmetry is the operation's, so it survives the repeatable carrier unchanged: the
target-kind certificate admits `True` and refuses `False` with the measured Kernel diagnostic. -/
example : ((checkRepeatableBooleanConstantComputation
      repeatableModel ["Probe"] taskConfirmed.id true).toOption.isSome,
    match checkRepeatableBooleanConstantComputation
        repeatableModel ["Probe"] taskConfirmed.id false with
    | .error cause => cause.diagnostic?
    | .ok _ => none) =
    (true, some .invalidCompareToYes) := by
  native_decide

/- A fixed target is refused by this carrier, which is what keeps the two families separate rather
than one widened gate: the fixed route above still owns that shape. -/
example : (checkRepeatableBooleanConstantComputation
    repeatableModel ["Probe"] formLevel.id true).toOption.isSome = false := by
  native_decide

end A12Kernel.Conformance.BooleanConstantComputation
