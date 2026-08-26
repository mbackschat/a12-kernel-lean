import A12Kernel.Elaboration.StringComputationRunApplication

/-! # Finite two-level String result application locks -/

namespace A12Kernel.Conformance.StringComputationNestedApplication

open A12Kernel

private def nestedString (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Order", "Outer", "Inner"]
  repeatableScope := [10, 20]
  policy := { kind := .string }
}

private def source := nestedString 1 "Source"
private def label := nestedString 2 "Label"
private def amount : FlatFieldDecl := {
  id := 3, name := "Amount", groupPath := ["Order", "Outer", "Inner"]
  repeatableScope := [10, 20]
  policy := { kind := .number { scale := 0, signed := false } }
}
private def outerLabel : FlatFieldDecl := {
  source with
  id := 4
  name := "OuterLabel"
  groupPath := ["Order", "Outer"]
  repeatableScope := [10]
}

private def model : FlatModel := {
  fields := [source, label, amount, outerLabel]
  repeatableGroups := [{
    level := 10, path := ["Order", "Outer"], repeatability := some 3
  }, {
    level := 20, path := ["Order", "Outer", "Inner"], repeatability := some 4
  }, {
    level := 21, path := ["Order", "Outer", "Open"], repeatability := none
  }, {
    level := 30, path := ["OpenOuter"], repeatability := none
  }, {
    level := 31, path := ["OpenOuter", "Inner"], repeatability := some 2
  }]
}

private def checked? (document : DocumentData) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" document).toOption

private def outerRow (outer : Nat) : RowAddr := { group := 10, path := [outer] }
private def innerRow (outer inner : Nat) : RowAddr := {
  group := 20, path := [outer, inner]
}
private def address (field : FieldId) (outer inner : Nat) : CellAddr := {
  field, path := [outer, inner]
}

private def empty? : Option (CheckedDocument model) := checked? {
  instantiatedRows := []
  cells := []
}

private def preserving? : Option (CheckedDocument model) := checked? {
  instantiatedRows := [
    outerRow 1, outerRow 2, outerRow 3,
    innerRow 3 1, innerRow 3 2]
  cells := [{
    address := address source.id 3 2
    stored := "KEEP"
    raw := .parsed (.str "KEEP")
  }]
}

private def erroredDestination? : Option (CheckedDocument model) := checked? {
  instantiatedRows := [outerRow 1, innerRow 1 1]
  cells := [{
    address := address label.id 1 1
    stored := "OLD"
    raw := .parsed (.str "OLD")
  }]
}

private def value (outer inner : Nat) (text : StoredString) :
    SourcedStringTargetOutcome CellAddr := {
  targetField := address label.id outer inner
  outcome := .accepted text
  source := .absent
}

private def cleared (outer inner : Nat) :
    SourcedStringTargetOutcome CellAddr := {
  targetField := address label.id outer inner
  outcome := .noValue
  source := .presentValue ⟨"old", by decide⟩
}

private def errored (outer inner : Nat) :
    SourcedStringTargetOutcome CellAddr := {
  targetField := address label.id outer inner
  outcome := .errored ⟨"TOO-LONG", by decide⟩ .tooLong
  source := .presentValue ⟨"old", by decide⟩
}

private def view (entries : List (SourcedStringTargetOutcome CellAddr)) :
    StringComputationRunView Bool CellAddr :=
  StringComputationRunView.fromSourcedOutcomes [] entries

private def expectedLeaves := [
  innerRow 1 1, innerRow 1 2,
  innerRow 3 1, innerRow 3 2, innerRow 3 3, innerRow 3 4]

private def topologyMatrixHolds : Bool := (do
  let empty ← empty?
  let preserving ← preserving?
  let erroredDestination ← erroredDestination?
  let reverse ← (view [cleared 1 2, value 3 4 ⟨"C", by decide⟩])
    |>.applyToCheckedTwoLevel empty 10 20 |>.toOption
  let forward ← (view [value 1 2 ⟨"A", by decide⟩, cleared 3 4])
    |>.applyToCheckedTwoLevel empty 10 20 |>.toOption
  let preserved ← (view [cleared 1 2, value 3 4 ⟨"C", by decide⟩])
    |>.applyToCheckedTwoLevel preserving 10 20 |>.toOption
  let rejected ← (view [errored 3 4])
    |>.applyToCheckedTwoLevel empty 10 20 |>.toOption
  let erroredExisting ← (view [errored 1 1])
    |>.applyToCheckedTwoLevel erroredDestination 10 20 |>.toOption
  pure (
    reverse.outerRows == [outerRow 1, outerRow 2, outerRow 3] &&
    reverse.innerRowsAt 1 == [innerRow 1 1, innerRow 1 2] &&
    reverse.innerRowsAt 2 == [] &&
    reverse.innerRowsAt 3 == expectedLeaves.drop 2 &&
    reverse.leafRows == expectedLeaves &&
    reverse.stateAt (address label.id 1 1) == StringTargetState.absent &&
    reverse.stateAt (address label.id 1 2) == StringTargetState.presentEmpty &&
    reverse.stateAt (address label.id 3 4) ==
      StringTargetState.presentValue ⟨"C", by decide⟩ &&
    forward.leafRows == expectedLeaves &&
    forward.stateAt (address label.id 1 2) ==
      StringTargetState.presentValue ⟨"A", by decide⟩ &&
    forward.stateAt (address label.id 3 4) == StringTargetState.presentEmpty &&
    preserved.stateAt (address source.id 3 2) ==
      StringTargetState.presentValue ⟨"KEEP", by decide⟩ &&
    rejected.outerRows == [] && rejected.leafRows == [] &&
    rejected.stateAt (address label.id 3 4) == StringTargetState.absent &&
    erroredExisting.outerRows == [outerRow 1] &&
    erroredExisting.innerRowsAt 1 == [innerRow 1 1] &&
    erroredExisting.stateAt (address label.id 1 1) ==
      StringTargetState.presentEmpty)
  ).getD false

/- Two-level String application pads predecessors only in the addressed parent, keeps exact action coordinates and String states, preserves destination cells, clears an existing ERRORED target, and does not materialize an absent one. -/
example : topologyMatrixHolds = true := by
  native_decide

private def nonemptyRows
    (projection : StringComputationTwoLevelApplicationProjection model) :
    List CellAddr :=
  projection.leafRows.filterMap fun row => match row.path with
    | [outer, inner] =>
        let target := address label.id outer inner
        match projection.stateAt target with
        | .presentValue text => if text.text.isEmpty then none else some target
        | .absent | .presentEmpty => none
    | _ => none

private def laterValidation? : Option (List CellAddr) := do
  let destination ← empty?
  let applied ← (view [
      value 1 2 ⟨"AA", by decide⟩,
      value 3 4 ⟨"CCC", by decide⟩])
    |>.applyToCheckedTwoLevel destination 10 20 |>.toOption
  pure (nonemptyRows applied)

/- The explicit later String-row decision sees only the two applied values at their exact nested addresses. -/
example : laterValidation? =
    some [address label.id 1 2, address label.id 3 4] := by
  native_decide

private def applicationError? (entry : SourcedStringTargetOutcome CellAddr) :
    Option StringComputationRepeatableApplicationError := do
  let destination ← empty?
  match (view [entry]).applyToCheckedTwoLevel destination 10 20 with
  | .error error => some error
  | .ok _ => none

private def topologyError? (outer inner : RepeatableLevel) :
    Option StringComputationRepeatableApplicationError := do
  let destination ← empty?
  match (view []).applyToCheckedTwoLevel destination outer inner with
  | .error error => some error
  | .ok _ => none

/- The bounded route refuses both over-capacity coordinates, wrong kind, scope, depth, and zero through ERRORED, plus unknown, reversed, and unbounded topology. -/
example :
    let numberTarget : SourcedStringTargetOutcome CellAddr := {
      cleared 1 1 with targetField := address amount.id 1 1 }
    let outerTarget : SourcedStringTargetOutcome CellAddr := {
      cleared 1 1 with targetField := { field := outerLabel.id, path := [1] } }
    let deepTarget : SourcedStringTargetOutcome CellAddr := {
      cleared 1 1 with targetField := { field := label.id, path := [1, 1, 1] } }
    let zeroErrored : SourcedStringTargetOutcome CellAddr := {
      errored 1 1 with targetField := address label.id 1 0 }
    let zeroOuterErrored : SourcedStringTargetOutcome CellAddr := {
      errored 1 1 with targetField := address label.id 0 1 }
    applicationError? (cleared 4 1) =
        some (.overCapacityTarget (address label.id 4 1) 3) ∧
      applicationError? (cleared 1 5) =
        some (.overCapacityTarget (address label.id 1 5) 4) ∧
      applicationError? numberTarget =
        some (.nonStringTarget numberTarget.targetField) ∧
      applicationError? outerTarget =
        some (.invalidTwoLevelScope outerTarget.targetField 10 20) ∧
      applicationError? deepTarget =
        some (.invalidTargetDepth deepTarget.targetField 2) ∧
      applicationError? zeroErrored =
        some (.zeroTargetCoordinate zeroErrored.targetField) ∧
      applicationError? zeroOuterErrored =
        some (.zeroTargetCoordinate zeroOuterErrored.targetField) ∧
      topologyError? 99 20 = some (.unknownRepeatableLevel 99) ∧
      topologyError? 10 99 = some (.unknownRepeatableLevel 99) ∧
      topologyError? 20 10 = some (.unsupportedTwoLevelDestination 20 10) ∧
      topologyError? 30 31 = some (.unboundedRepeatableLevel 30) ∧
      topologyError? 10 21 = some (.unboundedRepeatableLevel 21) := by
  native_decide

end A12Kernel.Conformance.StringComputationNestedApplication
