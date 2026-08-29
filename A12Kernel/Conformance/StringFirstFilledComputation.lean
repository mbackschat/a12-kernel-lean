import A12Kernel.Elaboration.StringFirstFilledComputation

/-! # Direct one-star ordinary String `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.StringFirstFilledComputation

open A12Kernel

private def stringField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := [])
    (policy : StringFieldPolicy := {}) : FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .string }
  stringPolicy := policy
}

private def target := stringField 1 ["Review"] "FirstCode" [] { maxLength := some 3 }
private def source := stringField 2 ["Review", "Rows"] "Code" [10]
private def repeatedTarget := stringField 3 ["Review", "Rows"] "Repeated" [10]
private def rawSource : FlatFieldDecl := {
  stringField 4 ["Review", "Rows"] "Raw" [10]
      { lineBreaksPermitted := true } with
  stringValueMode := .raw
}
private def customSource : FlatFieldDecl := {
  stringField 5 ["Review", "Rows"] "Custom" [10] with
  customType := some { name := "ReviewCode" }
}
private def nestedSource := stringField 6 ["Review", "Rows", "Details"] "Nested" [10, 20]
private def unrelated := stringField 7 ["Review"] "Unrelated"

private def customTarget : FlatFieldDecl := {
  stringField 8 ["Review"] "CustomTarget" with
  customType := some { name := "ReviewCode" }
}
private def rawTarget : FlatFieldDecl := {
  stringField 9 ["Review"] "RawTarget" [] { lineBreaksPermitted := true } with
  stringValueMode := .raw
}
private def patternTarget : FlatFieldDecl := {
  stringField 10 ["Review"] "PatternTarget" with
  stringPatternSource := some "A+"
}

private def model : FlatModel := {
  fields := [target, source, repeatedTarget, rawSource, customSource,
    nestedSource, unrelated, customTarget, rawTarget, patternTarget,
]
  repeatableGroups := [
    { level := 10, path := ["Review", "Rows"], repeatability := some 3 },
    { level := 20, path := ["Review", "Rows", "Details"], repeatability := some 2 }]
}

private def star (field : String) : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Review" }, { name := "Rows", starred := true }]
  field
}

private def nestedStar : SurfaceStarFieldPath := {
  base := .absolute
  groups := [{ name := "Review" }, { name := "Rows", starred := true },
    { name := "Details", starred := true }]
  field := nestedSource.name
}

private def checked? (targetField : FieldId) (authored : SurfaceStarFieldPath) :=
  (checkStringFirstFilledComputation model ["Review"] targetField authored).toOption

/-- The same check with the declaring group varied instead of the target, which is how a target
outside the declaring group is expressed under a single model root. -/
private def checkedAt? (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :=
  (checkStringFirstFilledComputation model declaringGroup targetField authored).toOption

private def customValidator : RegisteredCustomFieldValidator := fun _ _ => none

private def world : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ReviewCode" then some customValidator else none
}

private def patternCompiler : StringPatternCompiler := fun pattern =>
  if pattern == "A+" then
    some fun value =>
      !value.isEmpty && value.toList.all fun character => character == 'A'
  else
    none

private def prepared :
    PreparedFlatStringContext model patternCompiler :=
  (prepareFlatStringContext world patternCompiler model).toOption.get
    (by native_decide)

private def placed (field : FlatFieldDecl) (stored : String)
    (raw : RawCell) (path : List Nat := []) : ClassifiedCellInput := {
  address := { field := field.id, path }
  stored
  raw
}

private def document? (targetStored : Option String)
    (sourceCell : Option ClassifiedCellInput)
    (unrelatedStored : String := "KEEP") : Option (CheckedDocument model) :=
  checkDocument prepared "en_US" {
    instantiatedRows := [{ group := 10, path := [1] }]
    cells := (targetStored.map fun stored =>
        placed target stored (.parsed (.str stored))).toList ++
      sourceCell.toList ++
      [placed unrelated unrelatedStored (.parsed (.str unrelatedStored))]
  } |>.toOption

private def sourceText (stored : String) : ClassifiedCellInput :=
  placed source stored (.parsed (.str stored)) [1]

private def sourceMalformed : ClassifiedCellInput :=
  placed source "7" (.parsed (.num 7)) [1]

private def outcomeFor? (targetField : FieldId)
    (sourceCell : Option ClassifiedCellInput) :
    Option StringTargetOutcome := do
  let operation ← checked? targetField (star source.name)
  let input ← document? (some "OLD") sourceCell
  operation.execute prepared.patterns input |>.toOption

private def outcome? (sourceCell : Option ClassifiedCellInput) :
    Option StringTargetOutcome :=
  outcomeFor? target.id sourceCell

/- The checked boundary retains only a fixed ordinary evaluated-String target and a direct single-level ordinary String star. Placement is not part of that boundary. Declaring at `["Review", "Rows"]` puts the fixed target *above* the declaring group, which the checkpoint's `star-rowgroup` row measures as admitted: a star aggregate derives no iteration, so the Kernel's containment gate cannot fire. An unrepresentable declaring group is still refused, and the repeatable target is refused on the fixed-target gate rather than on placement. Varying the declaring group rather than the target's group keeps the fixture to one model root, as an authored A12 model is. -/
example :
    (checked? target.id (star source.name)).isSome = true ∧
      (checkedAt? ["Review", "Rows"] target.id (star source.name)).isSome = true ∧
      (checkedAt? [] target.id (star source.name)).isNone = true ∧
      (checked? patternTarget.id (star source.name)).isSome = true ∧
      (checked? repeatedTarget.id (star source.name)).isNone = true ∧
      (checked? customTarget.id (star source.name)).isNone = true ∧
      (checked? rawTarget.id (star source.name)).isNone = true ∧
      (checked? target.id (star rawSource.name)).isNone = true ∧
      (checked? target.id (star customSource.name)).isNone = true ∧
      (checked? target.id nestedStar).isNone = true := by
  native_decide

/- Selection stays lazy and the ordinary target policy owns accepted, no-value, rejected, and poison outcomes. -/
example :
    outcome? none = some .noValue ∧
      outcome? (some (sourceText "A7")) =
        some (.accepted ⟨"A7", by decide⟩) ∧
      outcome? (some (sourceText "ABCD")) =
        some (.errored ⟨"ABCD", by decide⟩ .tooLong) ∧
      outcomeFor? patternTarget.id (some (sourceText "AA")) =
        some (.accepted ⟨"AA", by decide⟩) ∧
      outcomeFor? patternTarget.id (some (sourceText "AB")) =
        some (.errored ⟨"AB", by decide⟩ .pattern) ∧
      outcome? (some sourceMalformed) = some (.poison .malformed) := by
  native_decide

private structure ResultApplicationSummary where
  unchangedChanges : List (StringComputedInstance FieldId)
  changedValue : StringTargetState
  cleared : List FieldId
  clearedValue : StringTargetState
  rejectedErrors : List (StringComputedError FieldId)
  rejectedCleared : List FieldId
  rejectedValue : StringTargetState
  poisonCleared : List FieldId
  poisonValue : StringTargetState
  unrelatedValue : StringTargetState
  residual : List FormalCause
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← checked? target.id (star source.name)
  let unchangedInput ← document? (some "A7") (some (sourceText "A7"))
  let changedInput ← document? (some "OLD") (some (sourceText "A7"))
  let emptyInput ← document? (some "OLD") none
  let rejectedInput ← document? (some "OLD") (some (sourceText "ABCD"))
  let poisonInput ← document? (some "OLD") (some sourceMalformed)
  let destination ← document? (some "OLD") none
  let unchanged ← operation.executeResult prepared.patterns unchangedInput
    ([] : List FormalCause) |>.toOption
  let changed ← operation.executeResult prepared.patterns changedInput
    ([] : List FormalCause) |>.toOption
  let cleared ← operation.executeResult prepared.patterns emptyInput
    ([] : List FormalCause) |>.toOption
  let rejected ← operation.executeResult prepared.patterns rejectedInput
    ([] : List FormalCause) |>.toOption
  let poison ← operation.executeResult prepared.patterns poisonInput
    [.malformed] |>.toOption
  let changedApplied ← changed.applyToChecked destination |>.toOption
  let clearedApplied ← cleared.applyToChecked destination |>.toOption
  let rejectedApplied ← rejected.applyToChecked destination |>.toOption
  let poisonApplied ← poison.applyToChecked destination |>.toOption
  pure {
    unchangedChanges := unchanged.string.withChanges
    changedValue := changedApplied target.id
    cleared := cleared.string.cleared
    clearedValue := clearedApplied target.id
    rejectedErrors := rejected.string.withErrors
    rejectedCleared := rejected.string.cleared
    rejectedValue := rejectedApplied target.id
    poisonCleared := poison.string.cleared
    poisonValue := poisonApplied target.id
    unrelatedValue := changedApplied unrelated.id
    residual := poison.string.formalErrorsInOperands
  }

/- Result classification stays source-relative, target rejection remains payloadful, and application preserves unrelated destination state. -/
example : resultApplicationSummary? = some {
    unchangedChanges := []
    changedValue := .presentValue ⟨"A7", by decide⟩
    cleared := [target.id]
    clearedValue := .presentEmpty
    rejectedErrors := [{
      targetField := target.id
      attempted := ⟨"ABCD", by decide⟩
      cause := .tooLong
    }]
    rejectedCleared := []
    rejectedValue := .presentEmpty
    poisonCleared := [target.id]
    poisonValue := .presentEmpty
    unrelatedValue := .presentValue ⟨"KEEP", by decide⟩
    residual := [.malformed]
  } := by
  native_decide

end A12Kernel.Conformance.StringFirstFilledComputation
