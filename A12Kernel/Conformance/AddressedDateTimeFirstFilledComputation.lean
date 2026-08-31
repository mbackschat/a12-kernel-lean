import A12Kernel.Elaboration.AddressedDateTimeFirstFilledFormalInput

/-! # Exact-address repeatable DateTime `FirstFilledValue` locks -/

namespace A12Kernel.Conformance.AddressedDateTimeFirstFilledComputation

open A12Kernel

private def dateTimeField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (format : String := "yyyy-MM-dd'T'HH:mm:ss")
    (components : TemporalComponents := TemporalComponents.now) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal .dateTime components }
  temporalTargetPolicy := some { format }
}

private def source := dateTimeField 1 "Stamp"
  ["Projects", "Choices"] [10, 20]
private def timeSource : FlatFieldDecl := {
  id := 2, name := "Clock", groupPath := ["Projects", "Choices"]
  repeatableScope := [10, 20]
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" }
}
private def incompleteSource := dateTimeField 3 "IncompleteStamp"
  ["Projects", "Choices"] [10, 20] "yyyy-MM-dd'T'HH:mm:ss"
  { TemporalComponents.now with second := false }
private def target := dateTimeField 4 "SelectedStamp"
  ["Projects", "Tasks"] [10, 30]
private def incompleteTarget := dateTimeField 5 "IncompleteTarget"
  ["Projects", "Tasks"] [10, 30] "yyyy-MM-dd'T'HH:mm:ss"
  { TemporalComponents.now with second := false }
private def fixedTarget := dateTimeField 6 "FixedStamp" ["Summary"] []
private def unrelated := dateTimeField 7 "UnrelatedStamp" ["Summary"] []

private def model : FlatModel := {
  fields := [source, timeSource, incompleteSource, target, incompleteTarget,
    fixedTarget, unrelated]
  repeatableGroups := [
    { level := 10, path := ["Projects"], repeatability := some 4 },
    { level := 20, path := ["Projects", "Choices"], repeatability := some 3,
      indexField := some source.id },
    { level := 30, path := ["Projects", "Tasks"], repeatability := some 3 }]
  timeZoneId := "Europe/Berlin"
}

private def siblingStar (field : String) : SurfaceStarFieldPath := {
  base := .relative 1
  groups := [{ name := "Choices", starred := true }]
  field
}

private def operation? :
    Option (CheckedAddressedDateTimeFirstFilledComputation model) :=
  (checkAddressedDateTimeFirstFilledComputation model
    ["Projects", "Tasks"] target.id (siblingStar source.name)).toOption

private def elabError? (checked : Except
    AddressedDateTimeFirstFilledComputationElabError
    (CheckedAddressedDateTimeFirstFilledComputation model)) :=
  match checked with
  | .error cause => some cause
  | .ok _ => none

/- The checked boundary admits only a complete ISO DateTime source and target, and the target must be repeatable. -/
example : operation?.isSome = true ∧
    elabError? (checkAddressedDateTimeFirstFilledComputation model
      ["Projects", "Tasks"] target.id
      (siblingStar timeSource.name)) =
        some (.sourceCarrier timeSource.path) ∧
    elabError? (checkAddressedDateTimeFirstFilledComputation model
      ["Projects", "Tasks"] target.id
      (siblingStar incompleteSource.name)) =
        some (.sourceCarrier incompleteSource.path) ∧
    elabError? (checkAddressedDateTimeFirstFilledComputation model
      ["Projects", "Tasks"] incompleteTarget.id
      (siblingStar source.name)) =
        some (.targetPolicy (.components incompleteTarget.id
          { TemporalComponents.now with second := false })) ∧
    elabError? (checkAddressedDateTimeFirstFilledComputation model
      ["Summary"] fixedTarget.id (siblingStar source.name)) =
        some (.targetNotRepeatable fixedTarget.path) := by
  native_decide

private def prepared :
    PreparedFlatStringContext model builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def dateTimeValue (epochMillis : Int) (year : Int)
    (month day hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : RawCell :=
  .parsed (.temporal (.dateTime { epochMillis } { year, month, day }
    (clock hour minute second valid) .storedGregorian))

private def rows : List RowAddr := [
  { group := 10, path := [1] }, { group := 10, path := [2] },
  { group := 10, path := [3] }, { group := 10, path := [4] },
  { group := 20, path := [1, 1] }, { group := 20, path := [1, 2] },
  { group := 20, path := [2, 1] }, { group := 20, path := [4, 1] },
  { group := 20, path := [4, 2] },
  { group := 30, path := [1, 1] }, { group := 30, path := [1, 2] },
  { group := 30, path := [2, 1] }, { group := 30, path := [3, 1] },
  { group := 30, path := [4, 1] }]

private def cell (field : FieldId) (path : List Nat) (stored : String)
    (raw : RawCell) : ClassifiedCellInput := {
  address := { field, path }, stored, raw
}

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def documentWithRows? (selectedRows : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" {
    instantiatedRows := selectedRows, cells }).toOption

private def document? (cells : List ClassifiedCellInput) :
    Option (CheckedDocument model) :=
  documentWithRows? rows cells

private def input? : Option (CheckedDocument model) := document? [
  cell source.id [1, 2] "2001-02-03T04:05:06"
    (dateTimeValue 1717229472000 2001 2 3 4 5 6 (by decide)),
  cell source.id [2, 1] "2024-07-01T13:14:15"
    (dateTimeValue 1719832455000 2024 7 1 13 14 15 (by decide)),
  cell source.id [4, 1] "bad" (.rejected .dateFormat),
  cell source.id [4, 2] "2024-08-01T16:17:18"
    (dateTimeValue 1722521838000 2024 8 1 16 17 18 (by decide)),
  cell target.id [1, 1] "2024-06-01T10:11:12"
    (dateTimeValue 1717229472000 2024 6 1 10 11 12 (by decide)),
  cell target.id [1, 2] "2000-01-01T12:34:56"
    (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide)),
  cell target.id [3, 1] "2000-01-01T12:34:56"
    (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide)),
  cell target.id [4, 1] "2000-01-01T12:34:56"
    (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide))]

private def stored (text : String) (nonempty : text ≠ "" := by decide) :
    StoredDateTime := { text, nonempty }

/- Every physical target row scans only its enclosing project's sibling source extent, renders the selected instant in the model zone, and retains its exact target address. -/
example : (do
    let operation ← operation?
    let input ← input?
    let outcomes ← operation.execute input |>.toOption
    pure (outcomes.map fun entry => (entry.targetField, entry.outcome))) = some [
      (address target.id [1, 1], .accepted (stored "2024-06-01T10:11:12")),
      (address target.id [1, 2], .accepted (stored "2024-06-01T10:11:12")),
      (address target.id [2, 1], .accepted (stored "2024-07-01T13:14:15")),
      (address target.id [3, 1], .noValue),
      (address target.id [4, 1], .poison .dateFormat)] := by
  native_decide

/-- Every project that owns a `Choices` row here carries a filled source, so an in-capacity target
    row scans a value and only an excluded one can read `.noValue`. -/
private def overLimitSourceCells : List ClassifiedCellInput := [
  cell source.id [1, 1] "2024-06-01T10:11:12"
    (dateTimeValue 1717229472000 2024 6 1 10 11 12 (by decide)),
  cell source.id [2, 1] "2024-07-01T13:14:15"
    (dateTimeValue 1719832455000 2024 7 1 13 14 15 (by decide)),
  cell source.id [5, 1] "2024-08-01T16:17:18"
    (dateTimeValue 1722521838000 2024 8 1 16 17 18 (by decide))]

/-- Target rows reached by this operation, over the fixture's rows plus a supplied extension and the
    source cells that extension instantiates. -/
private def targetPathsWith (extra : List RowAddr)
    (cells : List ClassifiedCellInput) :
    Option (List (List Nat × DateTimeTargetOutcome)) := do
  let operation ← operation?
  let input ← documentWithRows? (rows ++ extra) cells
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map fun entry => (entry.targetField.path, entry.outcome))

/- **Over-limit exclusion reaches through an ancestor, and the excluded row is cleared.** `Projects`
   is declared `max 4` and `Tasks` `max 3`. A third task row in project 1 is in capacity and scans; a
   fourth takes `.noValue`; and a fifth project's task row takes `.noValue` too, although nothing
   about that task row's own coordinate is out of range. Measured on kernel 30.8.1 across both
   codegen strategies on this same two-level topology
   ([checkpoint](../../docs/SOURCES.md#src-over-limit-computation-target)), where a seeded excess row
   reports `cleared`. Every in-capacity row here has no source, so `.noValue` is also its scan
   result — the discriminator is the *presence* of the entry, which dropping the row would lose. -/
/- **An over-limit row clears where its in-capacity twin computes, and an over-limit ancestor does
   the same to a row whose own coordinate is fine.** `Tasks` is declared `max 3`: rows `[1, 3]` and
   `[1, 4]` sit in one project, read one filled source, and differ only in capacity — the first is
   accepted, the second reads `.noValue`, which the application projection clears. `Projects` is
   `max 4`: the fifth project's task row reads `.noValue` although its own `Choices` source is filled
   and would have produced a value, so the exclusion is the ancestor's. Measured on kernel 30.8.1
   across both codegen strategies, where a seeded excess row reports `cleared`
   ([checkpoint](../../docs/SOURCES.md#src-over-limit-computation-target)). Dropping the row instead
   of clearing it passes every unseeded fixture and leaves a stale value. -/
example :
    (targetPathsWith [{ group := 30, path := [1, 3] }, { group := 30, path := [1, 4] }]
       overLimitSourceCells.dropLast,
      targetPathsWith [{ group := 10, path := [5] }, { group := 20, path := [5, 1] },
        { group := 30, path := [5, 1] }] overLimitSourceCells) =
    (some [([1, 1], .accepted (stored "2024-06-01T10:11:12")),
           ([1, 2], .accepted (stored "2024-06-01T10:11:12")),
           ([2, 1], .accepted (stored "2024-07-01T13:14:15")),
           ([3, 1], .noValue), ([4, 1], .noValue),
           ([1, 3], .accepted (stored "2024-06-01T10:11:12")),
           ([1, 4], .noValue)],
     some [([1, 1], .accepted (stored "2024-06-01T10:11:12")),
           ([1, 2], .accepted (stored "2024-06-01T10:11:12")),
           ([2, 1], .accepted (stored "2024-07-01T13:14:15")),
           ([3, 1], .noValue), ([4, 1], .noValue), ([5, 1], .noValue)]) := by
  native_decide

private structure ResultApplicationSummary where
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  cleared : List CellAddr
  residual : List FormalCause
  row11 : DateTimeTargetState
  row12 : DateTimeTargetState
  row21 : DateTimeTargetState
  row31 : DateTimeTargetState
  row41 : DateTimeTargetState
  unrelatedState : DateTimeTargetState
  deriving Repr, DecidableEq

private def resultApplicationSummary? : Option ResultApplicationSummary := do
  let operation ← operation?
  let input ← input?
  let destination ← document? [
    cell target.id [1, 1] "2000-01-01T12:34:56"
      (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide)),
    cell unrelated.id [] "2024-04-01T06:00:00"
      (dateTimeValue 1711944000000 2024 4 1 6 0 0 (by decide))]
  let result ← operation.executeResult input [.dateFormat] |>.toOption
  let applied ← result.applyToChecked destination |>.toOption
  pure {
    values := result.dateTime.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.dateTime.withChanges.map fun item =>
      (item.targetField, item.value.text)
    cleared := result.dateTime.cleared
    residual := result.dateTime.formalErrorsInOperands
    row11 := applied (address target.id [1, 1])
    row12 := applied (address target.id [1, 2])
    row21 := applied (address target.id [2, 1])
    row31 := applied (address target.id [3, 1])
    row41 := applied (address target.id [4, 1])
    unrelatedState := applied (address unrelated.id [])
  }

/- Result classification stays source-relative, while application mutates only retained exact-address actions in the separate destination projection. -/
example : resultApplicationSummary? = some {
    values := [
      (address target.id [1, 1], "2024-06-01T10:11:12"),
      (address target.id [1, 2], "2024-06-01T10:11:12"),
      (address target.id [2, 1], "2024-07-01T13:14:15")]
    changes := [
      (address target.id [1, 2], "2024-06-01T10:11:12"),
      (address target.id [2, 1], "2024-07-01T13:14:15")]
    cleared := [address target.id [3, 1], address target.id [4, 1]]
    residual := [.dateFormat]
    row11 := .presentValue (stored "2000-01-01T12:34:56")
    row12 := .presentValue (stored "2024-06-01T10:11:12")
    row21 := .presentValue (stored "2024-07-01T13:14:15")
    row31 := .presentEmpty
    row41 := .presentEmpty
    unrelatedState := .presentValue (stored "2024-04-01T06:00:00")
  } := by
  native_decide

private def formalFinding (path : List Nat)
    (cause : FormalCause) : ComputationFormalInputFinding := {
  address := address source.id path
  cause
}

private structure FormalInputSummary where
  planOperands : List FieldId
  planTargets : List FieldId
  findingsExact : Bool
  values : List (CellAddr × String)
  changes : List (CellAddr × String)
  errorsEmpty : Bool
  cleared : List CellAddr
  deriving Repr, DecidableEq

private def formalInputSummary? : Option FormalInputSummary := do
  let operation ← operation?
  let plan ← operation.formalInputPlan.toOption
  let input ← documentWithRows? [
      { group := 10, path := [1] }, { group := 10, path := [2] },
      { group := 20, path := [1, 1] },
      { group := 20, path := [2, 1] },
      { group := 20, path := [2, 2] },
      { group := 30, path := [1, 1] },
      { group := 30, path := [2, 1] }] [
    cell source.id [1, 1] "UNRENDERED-STAMP"
      (dateTimeValue 1717229472000 2001 2 3 4 5 6 (by decide)),
    cell source.id [2, 1] "DUPLICATE-STORED-KEY"
      (dateTimeValue 1719832455000 1991 2 3 4 5 6 (by decide)),
    cell source.id [2, 2] "DUPLICATE-STORED-KEY"
      (dateTimeValue 1722521838000 1981 2 3 4 5 6 (by decide)),
    cell target.id [1, 1] "2000-01-01T12:34:56"
      (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide)),
    cell target.id [2, 1] "2000-01-01T12:34:56"
      (dateTimeValue 946726496000 2000 1 1 12 34 56 (by decide))]
  let result ← operation.executeResultWithFormalInputs input |>.toOption
  let findings := result.dateTime.formalErrorsInOperands
  pure {
    planOperands := plan.operandFields
    planTargets := plan.computedFields
    findingsExact := findings.length == 2 &&
      findings.contains (formalFinding [2, 1] .duplicateIndex) &&
      findings.contains (formalFinding [2, 2] .duplicateIndex)
    values := result.dateTime.withoutErrors.map fun item =>
      (item.targetField, item.value.text)
    changes := result.dateTime.withChanges.map fun item =>
      (item.targetField, item.value.text)
    errorsEmpty := result.dateTime.withErrors.isEmpty
    cleared := result.dateTime.cleared
  }

/- Selected DateTime-index preparation compares stored identity, while a clean computation selects instant identity, ignores cached wall-label parts, and renders in the target's model zone. Duplicate keys poison only their reached parent-local scan. -/
example : formalInputSummary? = some {
    planOperands := [source.id]
    planTargets := [target.id]
    findingsExact := true
    values := [(address target.id [1, 1], "2024-06-01T10:11:12")]
    changes := [(address target.id [1, 1], "2024-06-01T10:11:12")]
    errorsEmpty := true
    cleared := [address target.id [2, 1]]
  } := by
  native_decide

end A12Kernel.Conformance.AddressedDateTimeFirstFilledComputation
