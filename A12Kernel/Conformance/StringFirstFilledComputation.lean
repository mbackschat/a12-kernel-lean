import A12Kernel.Elaboration.DocumentComputationStep

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

private def minimumTarget := stringField 11 ["Review"] "Minimum" []
  { minLength := some 2 }

private def model : FlatModel := {
  fields := [target, source, repeatedTarget, rawSource, customSource,
    nestedSource, unrelated, customTarget, rawTarget, patternTarget, minimumTarget,
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
  (checkStringFirstFilledComputation model ["Review"] targetField ⟨.star authored, []⟩).toOption

/-- The same check with the declaring group varied instead of the target, which is how a target
outside the declaring group is expressed under a single model root. -/
private def checkedAt? (declaringGroup : GroupPath) (targetField : FieldId)
    (authored : SurfaceStarFieldPath) :=
  (checkStringFirstFilledComputation model declaringGroup targetField ⟨.star authored, []⟩).toOption

private def customValidator : RegisteredCustomFieldValidator := fun _ _ => none

private def world : World := {
  now := { epochMillis := 0 }
  customFieldValidator? := fun name =>
    if name == "ReviewCode" then some customValidator else none
}

private def patternCompiler : StringPatternCompiler := fun pattern =>
  if pattern == "A+" then
    .compiled fun value =>
      !value.isEmpty && value.toList.all fun character => character == 'A'
  else
    .rejected

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
  let outcomes ← operation.execute prepared.patterns input |>.toOption
  (·.outcome) <$> outcomes.head?

private def outcome? (sourceCell : Option ClassifiedCellInput) :
    Option StringTargetOutcome :=
  outcomeFor? target.id sourceCell

example : (do
    let operation ← checked? target.id (star source.name)
    let input ← document? (some "AAA") (some (sourceText "AAA"))
    let data := { input.source with cells := input.source.cells.map fun cell =>
      { cell with sourceRepresentation := .unconvertedText } }
    let checked ← (checkDocument prepared "en_US" data).toOption
    let result ← operation.executeResult prepared.patterns checked
      ([] : List FormalCause) |>.toOption
    pure (checked.sourceStringTargetState target.id,
      result.string.withoutErrors.map (·.value.text),
      result.string.withChanges)) =
        some (.presentValue ⟨"AAA", by decide⟩, ["AAA"], []) := by
  native_decide

/- The checked boundary retains an ordinary evaluated-String target and an ordinary String source. A fixed target's placement is unrestricted: declaring at `["Review", "Rows"]` puts it *above* the declaring group, which the checkpoint's `star-rowgroup` row measures as admitted, a star aggregate deriving no iteration. An unrepresentable declaring group is still refused. The repeatable target inside the declaring group is admitted, its star over its own group reading the whole list at every row as the Kernel does ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-repeatable-computation-row-extent) `rerun`). Nested stars reuse that same checked source boundary. -/
example :
    (checked? target.id (star source.name)).isSome = true ∧
      (checkedAt? ["Review", "Rows"] target.id (star source.name)).isSome = true ∧
      (checkedAt? [] target.id (star source.name)).isNone = true ∧
      (checked? patternTarget.id (star source.name)).isSome = true ∧
      (checked? repeatedTarget.id (star source.name)).isSome = true ∧
      (checked? customTarget.id (star source.name)).isNone = true ∧
      (checked? rawTarget.id (star source.name)).isNone = true ∧
      (checked? target.id (star rawSource.name)).isNone = true ∧
      (checked? target.id (star customSource.name)).isNone = true ∧
      (checked? target.id nestedStar).isSome = true := by
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
  unchangedChanges : List (StringComputedInstance CellAddr)
  changedValue : StringTargetState
  cleared : List CellAddr
  clearedValue : StringTargetState
  rejectedErrors : List (StringComputedError CellAddr)
  rejectedCleared : List CellAddr
  rejectedValue : StringTargetState
  poisonCleared : List CellAddr
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
    changedValue := changedApplied { field := target.id, path := [] }
    cleared := cleared.string.cleared
    clearedValue := clearedApplied { field := target.id, path := [] }
    rejectedErrors := rejected.string.withErrors
    rejectedCleared := rejected.string.cleared
    rejectedValue := rejectedApplied { field := target.id, path := [] }
    poisonCleared := poison.string.cleared
    poisonValue := poisonApplied { field := target.id, path := [] }
    unrelatedValue := changedApplied { field := unrelated.id, path := [] }
    residual := poison.string.formalErrorsInOperands
  }

/- Result classification stays source-relative, target rejection remains payloadful, and application preserves unrelated destination state. -/
example : resultApplicationSummary? = some {
    unchangedChanges := []
    changedValue := .presentValue ⟨"A7", by decide⟩
    cleared := [{ field := target.id, path := [] }]
    clearedValue := .presentEmpty
    rejectedErrors := [{
      targetField := { field := target.id, path := [] }
      attempted := ⟨"ABCD", by decide⟩
      cause := .tooLong
    }]
    rejectedCleared := []
    rejectedValue := .presentEmpty
    poisonCleared := [{ field := target.id, path := [] }]
    poisonValue := .presentEmpty
    unrelatedValue := .presentValue ⟨"KEEP", by decide⟩
    residual := [.malformed]
  } := by
  native_decide

private structure RuntimeProjection where
  changes : List String := []
  errors : List (String × StringTargetError) := []
  cleared : Bool := false
  deriving Repr, DecidableEq

private def runtimeProjection? (targetField : FieldId)
    (sourceTexts : List (Option String)) (targetStored : Option String) :
    Option RuntimeProjection := do
  let operation ← checked? targetField (star source.name)
  let targetDecl ← (model.lookupUniqueId targetField).toOption
  let sourceCells := sourceTexts.zipIdx |>.flatMap fun (text, index) =>
    (text.map fun stored =>
      placed source stored (.parsed (.str stored)) [index + 1]).toList
  let input ← (checkDocument prepared "en_US" {
    instantiatedRows := sourceTexts.zipIdx |>.map fun (_, index) =>
      { group := 10, path := [index + 1] }
    cells := sourceCells ++ (targetStored.map fun stored =>
      placed targetDecl stored (.parsed (.str stored))).toList
  }).toOption
  let result ← operation.executeResult prepared.patterns input
    ([] : List FormalCause) |>.toOption
  pure {
    changes := result.string.withChanges.map (·.value.text)
    errors := result.string.withErrors.map fun item => (item.attempted.text, item.cause)
    cleared := !result.string.cleared.isEmpty
  }

example :
    runtimeProjection? target.id [none, some "AAA"] none =
      some { changes := ["AAA"] } ∧
    runtimeProjection? target.id [some "AAA"] (some "AAA") =
      some {} ∧
    runtimeProjection? target.id [none] (some "AA") =
      some { cleared := true } ∧
    runtimeProjection? target.id [none] none = some {} ∧
    runtimeProjection? target.id [] (some "AA") = some { cleared := true } := by
  native_decide

example :
    runtimeProjection? patternTarget.id [some "B"] (some "AA") =
      some { errors := [("B", .pattern)] } ∧
    runtimeProjection? target.id [some "AAAA"] (some "AA") =
      some { errors := [("AAAA", .tooLong)] } ∧
    runtimeProjection? minimumTarget.id [some "A"] (some "AA") =
      some { errors := [("A", .tooShort)] } := by
  native_decide

example :
    runtimeProjection? target.id [some "A\n", some "AAA"] (some "AA") =
      some { cleared := true } ∧
    runtimeProjection? target.id [some "AAA", some "A\n"] (some "AA") =
      some { changes := ["AAA"] } := by
  native_decide

/- `Rows*/Details/Nested` leaves `Details` unstarred below the first star, which the Kernel refuses
   with the missing-star class on this carrier in its two-operand form, beside a root String
   ([checkpoint](../../docs/sources/group-list-and-capacity-probes.md#src-computation-star-binding-gate));
   this lock isolates the path's class with a sole source. -/
example :
    let belowStar : SurfaceStarFieldPath := {
      base := .absolute
      groups := [{ name := "Review" }, { name := "Rows", starred := true }, { name := "Details" }]
      field := nestedSource.name }
    (match checkStringFirstFilledComputation model ["Review"] target.id ⟨.star belowStar, []⟩ with
      | .error error => error.diagnostic?
      | .ok _ => none) = some .noWildcard := by
  native_decide

private def plainEntry (field : String) : SurfaceFieldEntityOperand :=
  .field { base := .relative 0, groups := [], field }

private def listChecked? (targetField : FieldId) (entries : List SurfaceFieldEntityOperand) :
    Except StringFirstFilledComputationElabError (CheckedStringFirstFilledComputation model) :=
  match entries with
  | [] => .error (.source (.shape .tooFewFields))
  | first :: rest => checkStringFirstFilledComputation model ["Review"] targetField { first, rest }

/- A list is the shared entity list: a lone field is too few, a star beside a field is read in authored
order, measured for String prefix/fallback operands beside nested stars
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-nested-string-first-filled)), a
Custom member retains its distinct carrier refusal, and a list naming the target is the target-read
class, as the Kernel reports for a String `FirstFilledValue` listing its target. -/
example :
    ((listChecked? patternTarget.id [plainEntry unrelated.name, plainEntry minimumTarget.name]).isOk &&
    (match listChecked? patternTarget.id [plainEntry unrelated.name] with
      | .error error => error.diagnostic? == some .paramSizeInvalidN
      | .ok _ => false) &&
    (listChecked? patternTarget.id [.star (star source.name), plainEntry unrelated.name]).isOk &&
    (match listChecked? patternTarget.id [plainEntry unrelated.name, plainEntry customTarget.name] with
      | .error (.unsupportedSourceCarrier _) => true
      | _ => false) &&
    (match listChecked? patternTarget.id [plainEntry unrelated.name, plainEntry patternTarget.name] with
      | .error error => error.diagnostic? == some .errorReferenceToCalculatedField &&
          (match error with | .targetSelfReference _ => true | _ => false)
      | .ok _ => false)) = true := by
  native_decide

/-- The pattern target's `FirstFilledValue(Unrelated, Minimum)` run as a plan step over a document
holding `text` in `Unrelated`, with the given matcher lookup. -/
private def stepOutcome? (matchers : StringTargetMatchers) (text : String) :
    Option (Except DocumentComputationStepFault DocumentTargetOutcome) := do
  let operation ← (listChecked? patternTarget.id
    [plainEntry unrelated.name, plainEntry minimumTarget.name]).toOption
  let data : DocumentData :=
    { instantiatedRows := [], cells := [placed unrelated text (.parsed (.str text))] }
  let document ← (checkDocument prepared "en_US" data).toOption
  pure (((← CheckedDocumentComputationStep.ofStringFirstFilled? operation).run world matchers document).map
    (·.1))

/- A plan step checks its String target against the prepared pattern it is handed, so `AB` is rejected
and `AA` accepted under `A+`, the rejection an errored write; a lookup holding no entry for the target is the step's structural fault,
never an unchecked write. Internal: no Kernel row is read. -/
example :
    ((match stepOutcome? prepared.patterns.targetMatcher? "AB" with
      | some (.ok (.string (.errored _ _))) => true
      | _ => false) &&
    (match stepOutcome? prepared.patterns.targetMatcher? "AA" with
      | some (.ok (.string (.accepted _))) => true
      | _ => false) &&
    (match stepOutcome? (fun _ => none) "AA" with
      | some (.error (.stringFirstFilled (.targetPatternUnavailable _))) => true
      | _ => false)) = true := by
  native_decide

end A12Kernel.Conformance.StringFirstFilledComputation
