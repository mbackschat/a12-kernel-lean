import A12Kernel.Elaboration.StringComputationRunApplication

/-! # Finite one-level String result application locks -/

namespace A12Kernel.Conformance.StringComputationRepeatableApplication

open A12Kernel

private def repeatedString (id : FieldId) (name : String) : FlatFieldDecl := {
  id, name, groupPath := ["Order", "Lines"]
  repeatableScope := [10]
  policy := { kind := .string }
}

private def source := repeatedString 1 "Source"
private def label := repeatedString 2 "Label"

private def amount : FlatFieldDecl := {
  id := 3, name := "Amount", groupPath := ["Order", "Lines"]
  repeatableScope := [10]
  policy := { kind := .number { scale := 0, signed := false } }
}

private def rootLabel : FlatFieldDecl := {
  id := 4, name := "RootLabel", groupPath := ["Order"]
  policy := { kind := .string }
}

private def model : FlatModel := {
  fields := [source, label, amount, rootLabel]
  repeatableGroups := [{
    level := 10, path := ["Order", "Lines"], repeatability := some 3
  }, {
    level := 11, path := ["Other"], repeatability := some 1
  }, {
    level := 12, path := ["Other", "Nested"], repeatability := some 1
  }, {
    level := 13, path := ["Open"], repeatability := none
  }]
}

private def checked? (document : DocumentData) : Option (CheckedDocument model) := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  (checkDocument prepared "en_US" document).toOption

private def row (index : Nat) : RowAddr := { group := 10, path := [index] }
private def address (field : FieldId) (index : Nat) : CellAddr :=
  { field, path := [index] }

private def empty? : Option (CheckedDocument model) := checked? {
  instantiatedRows := []
  cells := []
}

private def preserving? : Option (CheckedDocument model) := checked? {
  instantiatedRows := [row 1, row 2]
  cells := [{
    address := address source.id 2
    stored := "KEEP"
    raw := .parsed (.str "KEEP")
  }]
}

private def erroredDestination? : Option (CheckedDocument model) := checked? {
  instantiatedRows := [row 1]
  cells := [{
    address := address label.id 1
    stored := "OLD"
    raw := .parsed (.str "OLD")
  }]
}

private def value (index : Nat) (text : StoredString) :
    SourcedStringTargetOutcome CellAddr := {
  targetField := address label.id index
  outcome := .accepted text
  source := .absent
}

private def cleared (index : Nat) :
    SourcedStringTargetOutcome CellAddr := {
  targetField := address label.id index
  outcome := .noValue
  source := .presentValue ⟨"old", by decide⟩
}

private def errored (index : Nat) :
    SourcedStringTargetOutcome CellAddr := {
  targetField := address label.id index
  outcome := .errored ⟨"TOO-LONG", by decide⟩ .tooLong
  source := .presentValue ⟨"old", by decide⟩
}

private def view (entries : List (SourcedStringTargetOutcome CellAddr)) :
    StringComputationRunView Bool CellAddr :=
  StringComputationRunView.fromSourcedOutcomes [] entries

private def topologyMatrixHolds : Bool := (do
  let empty ← empty?
  let preserving ← preserving?
  let erroredDestination ← erroredDestination?
  let reverse ← (view [cleared 3, value 1 ⟨"A", by decide⟩])
    |>.applyToCheckedOneLevel empty 10 |>.toOption
  let forward ← (view [cleared 1, value 3 ⟨"C", by decide⟩])
    |>.applyToCheckedOneLevel empty 10 |>.toOption
  let preserved ← (view [cleared 3, value 1 ⟨"A", by decide⟩])
    |>.applyToCheckedOneLevel preserving 10 |>.toOption
  let rejected ← (view [errored 3])
    |>.applyToCheckedOneLevel empty 10 |>.toOption
  let erroredExisting ← (view [errored 1])
    |>.applyToCheckedOneLevel erroredDestination 10 |>.toOption
  pure (
    reverse.rows == [row 1, row 2, row 3] &&
    reverse.stateAt (address label.id 1) ==
      StringTargetState.presentValue ⟨"A", by decide⟩ &&
    reverse.stateAt (address label.id 2) == StringTargetState.absent &&
    reverse.stateAt (address label.id 3) == StringTargetState.presentEmpty &&
    forward.rows == [row 1, row 2, row 3] &&
    forward.stateAt (address label.id 1) == StringTargetState.presentEmpty &&
    forward.stateAt (address label.id 2) == StringTargetState.absent &&
    forward.stateAt (address label.id 3) ==
      StringTargetState.presentValue ⟨"C", by decide⟩ &&
    preserved.rows == [row 1, row 2, row 3] &&
    preserved.stateAt (address source.id 2) ==
      StringTargetState.presentValue ⟨"KEEP", by decide⟩ &&
    rejected.rows == [] &&
    rejected.stateAt (address label.id 3) == StringTargetState.absent &&
    erroredExisting.rows == [row 1] &&
    erroredExisting.stateAt (address label.id 1) ==
      StringTargetState.presentEmpty)
  ).getD false

/- One-level String application pads the complete predecessor prefix, keeps clear and value actions at their exact coordinates, preserves unrelated destination text, clears an existing ERRORED target, and does not materialize an absent ERRORED target. -/
example : topologyMatrixHolds = true := by
  native_decide

private def projectedStringRows
    (projection : StringComputationOneLevelApplicationProjection model) :
    List CellAddr :=
  projection.rows.filterMap fun selected => match selected.path with
    | [coordinate] =>
        let target := address label.id coordinate
        match projection.stateAt target with
        | .presentValue value => if value.text.isEmpty then none else some target
        | .absent | .presentEmpty => none
    | _ => none

private def laterValidation? : Option (List CellAddr) := do
  let destination ← empty?
  let applied ← (view [
      value 1 ⟨"A", by decide⟩,
      value 3 ⟨"CCC", by decide⟩])
    |>.applyToCheckedOneLevel destination 10 |>.toOption
  pure (projectedStringRows applied)

/- An explicit later String-row decision sees only the two applied values, not the padded empty predecessor. -/
example : laterValidation? =
    some [address label.id 1, address label.id 3] := by
  native_decide

private def applicationError?
    (entries : List (SourcedStringTargetOutcome CellAddr))
    (level : RepeatableLevel := 10) :
    Option StringComputationRepeatableApplicationError := do
  let destination ← empty?
  match (view entries).applyToCheckedOneLevel destination level with
  | .error error => some error
  | .ok _ => none

/- The bounded route fails closed on duplicate addresses, unknown, unsupported, or unbounded levels, non-String targets, invalid scope or depth, zero coordinates, and over-capacity coordinates. The zero-coordinate control travels through ERRORED application. -/
example :
    let duplicate := value 1 ⟨"A", by decide⟩
    let numberTarget : SourcedStringTargetOutcome CellAddr := {
      duplicate with targetField := address amount.id 1 }
    let rootTarget : SourcedStringTargetOutcome CellAddr := {
      duplicate with targetField := { field := rootLabel.id, path := [] } }
    let deepTarget : SourcedStringTargetOutcome CellAddr := {
      duplicate with targetField := { field := label.id, path := [1, 2] } }
    let zeroErrored : SourcedStringTargetOutcome CellAddr := {
      errored 1 with targetField := address label.id 0 }
    applicationError? [duplicate, duplicate] =
        some (.duplicateActionTarget duplicate.targetField) ∧
      applicationError? [] 99 = some (.unknownRepeatableLevel 99) ∧
      applicationError? [] 12 = some (.unsupportedOneLevelDestination 12) ∧
      applicationError? [] 13 = some (.unboundedRepeatableLevel 13) ∧
      applicationError? [numberTarget] =
        some (.nonStringTarget numberTarget.targetField) ∧
      applicationError? [rootTarget] =
        some (.invalidOneLevelScope rootTarget.targetField 10) ∧
      applicationError? [deepTarget] =
        some (.invalidTargetDepth deepTarget.targetField 1) ∧
      applicationError? [zeroErrored] =
        some (.zeroTargetCoordinate zeroErrored.targetField) ∧
      applicationError? [cleared 4] =
        some (.overCapacityTarget (address label.id 4) 3) := by
  native_decide

end A12Kernel.Conformance.StringComputationRepeatableApplication
