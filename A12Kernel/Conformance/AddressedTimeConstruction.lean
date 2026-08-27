import A12Kernel.Elaboration.AddressedWorldTimeConstruction

/-! # Repeatable addressed `Time(...)` construction locks -/

namespace A12Kernel.Conformance.AddressedTimeConstruction

open A12Kernel

private def numberComponent (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (maximum : Rat) : FlatFieldDecl := {
  id
  name
  groupPath
  repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := false } }
  numericTargetConstraints := { maximum := some maximum }
}

private def rootHour :=
  numberComponent 1 "RootHour" ["Order"] [] 23

private def projectMinute :=
  numberComponent 2 "ProjectMinute" ["Order", "Projects"] [10] 59

private def rowSecond :=
  numberComponent 3 "RowSecond" ["Order", "Projects", "Tasks"] [10, 20] 59

private def stringComponent (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id
  name
  groupPath
  repeatableScope := scope
  policy := { kind := .string }
  stringPolicy := { maxLength := some 2 }
  stringPatternSource := some "[0-9]+"
}

private def rootHourText :=
  stringComponent 7 "RootHourText" ["Order"] []

private def projectMinuteText :=
  stringComponent 8 "ProjectMinuteText" ["Order", "Projects"] [10]

private def rowSecondText :=
  stringComponent 9 "RowSecondText" ["Order", "Projects", "Tasks"] [10, 20]

private def temporalComponent (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel)
    (kind : TemporalKind) (components : TemporalComponents) (format : String) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .temporal kind components }
  temporalTargetPolicy := some { format }
}

private def rootStamp := temporalComponent 10 "RootStamp" ["Order"] [] .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss"

private def projectTime := temporalComponent 11 "ProjectTime" ["Order", "Projects"] [10] .time TemporalComponents.time "HH:mm:ss"

private def rowStamp := temporalComponent 12 "RowStamp" ["Order", "Projects", "Tasks"] [10, 20] .dateTime TemporalComponents.now "yyyy-MM-dd'T'HH:mm:ss"

private def target : FlatFieldDecl := {
  id := 4
  name := "SelectedTime"
  groupPath := ["Order", "Projects", "Tasks"]
  repeatableScope := [10, 20]
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" }
}

private def textSource : FlatFieldDecl := {
  id := 5
  name := "TextSource"
  groupPath := ["Order"]
  policy := { kind := .string }
  stringPolicy := { maxLength := some 2 }
}

private def siblingHour :=
  numberComponent 6 "SiblingHour" ["Order", "OtherRows"] [30] 23

private def model : FlatModel := {
  fields := [rootHour, projectMinute, rowSecond, target, textSource, siblingHour,
    rootHourText, projectMinuteText, rowSecondText, rootStamp, projectTime, rowStamp]
  repeatableGroups := [
    { level := 10, path := ["Order", "Projects"], repeatability := some 3 },
    { level := 20, path := ["Order", "Projects", "Tasks"], repeatability := some 3 },
    { level := 30, path := ["Order", "OtherRows"], repeatability := some 3 }
  ]
}

private def absolute (groups : GroupPath) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def mixedComponents : SurfaceAddressedTimeComponents :=
  .second
    (.number (absolute ["Order"] "RootHour"))
    (.number (absolute ["Order", "Projects"] "ProjectMinute"))
    (.number (absolute ["Order", "Projects", "Tasks"] "RowSecond"))

private def mixedOperation? :
    Option (CheckedAddressedTimeConstructionComputation model) :=
  (checkAddressedTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id mixedComponents).toOption

private def stringComponents : SurfaceAddressedTimeComponents :=
  .second
    (.string (absolute ["Order"] "RootHourText"))
    (.string (absolute ["Order", "Projects"] "ProjectMinuteText"))
    (.string (absolute ["Order", "Projects", "Tasks"] "RowSecondText"))

private def stringOperation? :
    Option (CheckedAddressedTimeConstructionComputation model) :=
  (checkAddressedTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id stringComponents).toOption

private def extractorComponents : SurfaceAddressedTimeComponents :=
  .second
    (.extractor .hour (absolute ["Order"] "RootStamp"))
    (.extractor .minute (absolute ["Order", "Projects"] "ProjectTime"))
    (.extractor .second
      (absolute ["Order", "Projects", "Tasks"] "RowStamp"))

private def extractorOperation? :
    Option (CheckedAddressedTimeConstructionComputation model) :=
  (checkAddressedTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id extractorComponents).toOption

private def typedMix? :
    Option (CheckedAddressedTimeConstructionComputation model) :=
  (checkAddressedTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id
    (.second
      (.number (absolute ["Order"] "RootHour"))
      (.string (absolute ["Order", "Projects"] "ProjectMinuteText"))
      (.constant "9")))
    |>.toOption

private def extractorMix? :
    Option (CheckedAddressedTimeConstructionComputation model) :=
  (checkAddressedTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id
    (.second
      (.number (absolute ["Order"] "RootHour"))
      (.string (absolute ["Order", "Projects"] "ProjectMinuteText"))
      (.extractor .second
        (absolute ["Order", "Projects", "Tasks"] "RowStamp"))))
    |>.toOption

private def staticError? (components : SurfaceAddressedTimeComponents) :
    Option AddressedTimeConstructionElabError :=
  match checkAddressedTimeConstructionComputation model
      ["Order", "Projects", "Tasks"] target.id components with
  | .ok _ => none
  | .error cause => some cause

private def constantFieldMix? :
    Option (CheckedAddressedTimeConstructionComputation model) :=
  (checkAddressedTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id
    (.second
      (.number (absolute ["Order"] "RootHour"))
      (.constant "2")
      (.number (absolute ["Order", "Projects", "Tasks"] "RowSecond"))))
    |>.toOption

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def outerRow (outer : Nat) : RowAddr :=
  { group := 10, path := [outer] }

private def innerRow (outer inner : Nat) : RowAddr :=
  { group := 20, path := [outer, inner] }

private def address (field : FieldId) (path : List Nat) : CellAddr :=
  { field, path }

private def numberCell (field : FieldId) (path : List Nat) (value : Rat) :
    ClassifiedCellInput := {
  address := address field path
  stored := toString value
  raw := .parsed (.num value)
}

private def rejectedNumberCell (field : FieldId) (path : List Nat) :
    ClassifiedCellInput := {
  address := address field path
  stored := "60"
  raw := .rejected .declaredConstraint
}

private def stringCell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput := {
  address := address field path
  stored
  raw
}

private def timeCell (path : List Nat) (stored : String)
    (value : TimeOfDay) : ClassifiedCellInput := {
  address := address target.id path
  stored
  raw := .parsed (.temporal (.time { epochMillis := 0 } value))
}

private def temporalCell (field : FieldId) (path : List Nat)
    (stored : String) (value : TemporalValue) : ClassifiedCellInput := {
  address := address field path, stored, raw := .parsed (.temporal value) }

private def dateTimeValue (hour minute second : Nat) (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TemporalValue :=
  .dateTime { epochMillis := 0 } { year := 2024, month := 6, day := 1 } (clock hour minute second valid) .storedGregorian

private def timeValue (hour minute second : Nat) (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TemporalValue :=
  .time { epochMillis := 0 } (clock hour minute second valid)

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def document? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def correlationInput? := document? [
    outerRow 1, outerRow 2,
    innerRow 1 1, innerRow 1 2, innerRow 2 1] [
  numberCell rootHour.id [] 5,
  numberCell projectMinute.id [1] 2,
  numberCell projectMinute.id [2] 4,
  numberCell rowSecond.id [1, 1] 9,
  numberCell rowSecond.id [1, 2] 10,
  numberCell rowSecond.id [2, 1] 9,
  timeCell [1, 1] "05:02:09" (clock 5 2 9 (by decide)),
  timeCell [1, 2] "12:34:56" (clock 12 34 56 (by decide))]

private def emptyDestination? := document? [
  outerRow 1, outerRow 2,
  innerRow 1 1, innerRow 1 2, innerRow 2 1] []

private structure CorrelationSummary where
  dependencies : List FieldId
  successes : List (CellAddr × String)
  changes : List (CellAddr × String)
  cleared : List CellAddr
  applied : List (Bool × Option String)
  deriving Repr, DecidableEq

private structure OutcomeSummary where
  target : CellAddr
  value : Option String
  noValue : Bool
  poison : Option FormalCause
  deriving Repr, DecidableEq

private def summarizeOutcome
    (entry : AddressedTimeConstructionOutcome) : OutcomeSummary :=
  match entry.outcome with
  | .accepted value => {
      target := entry.targetField
      value := some value.text
      noValue := false
      poison := none
    }
  | .noValue => {
      target := entry.targetField
      value := none
      noValue := true
      poison := none
    }
  | .poison cause => {
      target := entry.targetField
      value := none
      noValue := false
      poison := some cause
    }

private structure MissingSummary where
  outcomes : List OutcomeSummary
  successes : List CellAddr
  changes : List CellAddr
  cleared : List CellAddr
  residual : List FormalCause
  applied : List (Bool × Option String)
  deriving Repr, DecidableEq

private def correlationResultFor?
    (operation? : Option (CheckedAddressedTimeConstructionComputation model))
    (input? : Option (CheckedDocument model)) : Option CorrelationSummary := do
  let operation ← operation?
  let input ← input?
  let view ← operation.executeResult input ([] : List FormalCause) |>.toOption
  let destination ← emptyDestination?
  let applied ← view.applyToChecked destination |>.toOption
  let summarize := fun (item : TimeComputedInstance CellAddr) =>
    (item.targetField, item.value.text)
  let summarizeState := fun (state : TimeTargetState) =>
    (TemporalTargetState.isPresent state,
      (TemporalTargetState.storedValue state).map StoredTemporalText.text)
  pure {
    dependencies := operation.fieldDependencies
    successes := view.time.withoutErrors.map summarize
    changes := view.time.withChanges.map summarize
    cleared := view.time.cleared
    applied := [
      summarizeState (applied (address target.id [1, 1])),
      summarizeState (applied (address target.id [1, 2])),
      summarizeState (applied (address target.id [2, 1]))
    ]
  }

private def correlationResult? : Option CorrelationSummary :=
  correlationResultFor? mixedOperation? correlationInput?

private def missingInput? := document? [
    outerRow 1, outerRow 2,
    innerRow 1 1, innerRow 2 1, innerRow 2 2, innerRow 2 3] [
  numberCell rootHour.id [] 5,
  numberCell projectMinute.id [2] 2,
  numberCell rowSecond.id [1, 1] 9,
  rejectedNumberCell rowSecond.id [2, 2],
  numberCell rowSecond.id [2, 3] 9,
  timeCell [1, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [2, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [2, 2] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [2, 3] "12:34:56" (clock 12 34 56 (by decide))]

private def missingDestination? := document? [
  outerRow 1, outerRow 2,
  innerRow 1 1, innerRow 2 1, innerRow 2 2, innerRow 2 3] []

private def missingResult? : Option MissingSummary := do
  let operation ← mixedOperation?
  let input ← missingInput?
  let outcomes ← operation.execute input |>.toOption
  let view ← operation.executeResult input [.declaredConstraint] |>.toOption
  let destination ← missingDestination?
  let applied ← view.applyToChecked destination |>.toOption
  let summarizeState := fun (state : TimeTargetState) =>
    (TemporalTargetState.isPresent state,
      (TemporalTargetState.storedValue state).map StoredTemporalText.text)
  pure {
    outcomes := outcomes.map summarizeOutcome
    successes := view.time.withoutErrors.map (·.targetField)
    changes := view.time.withChanges.map (·.targetField)
    cleared := view.time.cleared
    residual := view.time.formalErrorsInOperands
    applied := [[1, 1], [2, 1], [2, 2], [2, 3]].map fun path =>
      summarizeState (applied (address target.id path))
  }

private def earlierMissingInput? := document? [
    outerRow 1, innerRow 1 1, innerRow 1 2] [
  numberCell projectMinute.id [1] 2,
  rejectedNumberCell rowSecond.id [1, 1],
  numberCell rowSecond.id [1, 2] 9,
  timeCell [1, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [1, 2] "12:34:56" (clock 12 34 56 (by decide))]

private def earlierMissingOutcomes? : Option (List OutcomeSummary) := do
  let operation ← mixedOperation?
  let input ← earlierMissingInput?
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map summarizeOutcome)

private def stringCorrelationInput? := document? [
    outerRow 1, outerRow 2,
    innerRow 1 1, innerRow 1 2, innerRow 2 1] [
  stringCell rootHourText.id [] "05" (.parsed (.str "05")),
  stringCell projectMinuteText.id [1] "02" (.parsed (.str "02")),
  stringCell projectMinuteText.id [2] "04" (.parsed (.str "04")),
  stringCell rowSecondText.id [1, 1] "09" (.parsed (.str "09")),
  stringCell rowSecondText.id [1, 2] "10" (.parsed (.str "10")),
  stringCell rowSecondText.id [2, 1] "09" (.parsed (.str "09")),
  timeCell [1, 1] "05:02:09" (clock 5 2 9 (by decide)),
  timeCell [1, 2] "12:34:56" (clock 12 34 56 (by decide))]

private def stringCorrelationResult? : Option CorrelationSummary :=
  correlationResultFor? stringOperation? stringCorrelationInput?

private def extractorCorrelationInput? := document? [
    outerRow 1, outerRow 2,
    innerRow 1 1, innerRow 1 2, innerRow 2 1] [
  temporalCell rootStamp.id [] "2024-06-01T05:00:00"
    (dateTimeValue 5 0 0 (by decide)),
  temporalCell projectTime.id [1] "00:02:00" (timeValue 0 2 0 (by decide)),
  temporalCell projectTime.id [2] "00:04:00" (timeValue 0 4 0 (by decide)),
  temporalCell rowStamp.id [1, 1] "2024-06-01T00:00:09"
    (dateTimeValue 0 0 9 (by decide)),
  temporalCell rowStamp.id [1, 2] "2024-06-01T00:00:10"
    (dateTimeValue 0 0 10 (by decide)),
  temporalCell rowStamp.id [2, 1] "2024-06-01T00:00:09"
    (dateTimeValue 0 0 9 (by decide)),
  timeCell [1, 1] "05:02:09" (clock 5 2 9 (by decide)),
  timeCell [1, 2] "12:34:56" (clock 12 34 56 (by decide))]

private def extractorCorrelationResult? : Option CorrelationSummary :=
  correlationResultFor? extractorOperation? extractorCorrelationInput?

private def extractorFailureInput? := document? [
    outerRow 1, outerRow 2,
    innerRow 1 1, innerRow 2 1, innerRow 2 2, innerRow 2 3] [
  temporalCell rootStamp.id [] "2024-06-01T05:00:00"
    (dateTimeValue 5 0 0 (by decide)),
  temporalCell projectTime.id [2] "00:02:00" (timeValue 0 2 0 (by decide)),
  temporalCell rowStamp.id [1, 1] "2024-06-01T00:00:09"
    (dateTimeValue 0 0 9 (by decide)),
  { address := address rowStamp.id [2, 2], stored := "bad",
    raw := .rejected .dateFormat },
  temporalCell rowStamp.id [2, 3] "2024-06-01T00:00:09"
    (dateTimeValue 0 0 9 (by decide)),
  timeCell [1, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [2, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [2, 2] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [2, 3] "12:34:56" (clock 12 34 56 (by decide))]

private def extractorFailureOutcomes? : Option (List OutcomeSummary) := do
  let operation ← extractorOperation?
  let input ← extractorFailureInput?
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map summarizeOutcome)

private def earlierMissingExtractorInput? := document? [
    outerRow 1, innerRow 1 1, innerRow 1 2] [
  temporalCell projectTime.id [1] "00:02:00" (timeValue 0 2 0 (by decide)),
  { address := address rowStamp.id [1, 1], stored := "bad",
    raw := .rejected .dateFormat },
  temporalCell rowStamp.id [1, 2] "2024-06-01T00:00:09"
    (dateTimeValue 0 0 9 (by decide)),
  timeCell [1, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [1, 2] "12:34:56" (clock 12 34 56 (by decide))]

private def earlierMissingExtractorOutcomes? : Option (List OutcomeSummary) := do
  let operation ← extractorOperation?
  let input ← earlierMissingExtractorInput?
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map summarizeOutcome)

private def noTargetRowsExtractorOutcomes? : Option (List OutcomeSummary) := do
  let operation ← extractorOperation?
  let input ← document? [] [
    temporalCell rootStamp.id [] "2024-06-01T05:00:00"
      (dateTimeValue 5 0 0 (by decide))]
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map summarizeOutcome)

private def stringFailureInput? := document? [
    outerRow 1, outerRow 2,
    innerRow 1 1, innerRow 2 1, innerRow 2 2, innerRow 2 3] [
  stringCell rootHourText.id [] "05" (.parsed (.str "05")),
  stringCell projectMinuteText.id [2] "02" (.parsed (.str "02")),
  stringCell rowSecondText.id [1, 1] "09" (.parsed (.str "09")),
  stringCell rowSecondText.id [2, 2] "xx" (.rejected .declaredConstraint),
  stringCell rowSecondText.id [2, 3] "09" (.parsed (.str "09")),
  timeCell [1, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [2, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [2, 2] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [2, 3] "12:34:56" (clock 12 34 56 (by decide))]

private def stringFailureOutcomes? : Option (List OutcomeSummary) := do
  let operation ← stringOperation?
  let input ← stringFailureInput?
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map summarizeOutcome)

private def impossibleStringInput? := document? [
    outerRow 1, innerRow 1 1, innerRow 1 2] [
  stringCell rootHourText.id [] "05" (.parsed (.str "05")),
  stringCell projectMinuteText.id [1] "02" (.parsed (.str "02")),
  stringCell rowSecondText.id [1, 1] "99" (.parsed (.str "99")),
  stringCell rowSecondText.id [1, 2] "09" (.parsed (.str "09")),
  timeCell [1, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [1, 2] "12:34:56" (clock 12 34 56 (by decide))]

private def impossibleStringResult? :
    Option (List OutcomeSummary × List CellAddr × List CellAddr) := do
  let operation ← stringOperation?
  let input ← impossibleStringInput?
  let outcomes ← operation.execute input |>.toOption
  let view ← operation.executeResult input ([] : List FormalCause) |>.toOption
  pure (outcomes.map summarizeOutcome, view.time.cleared,
    view.time.withChanges.map (·.targetField))

private def earlierMissingStringInput? := document? [
    outerRow 1, innerRow 1 1, innerRow 1 2] [
  stringCell projectMinuteText.id [1] "02" (.parsed (.str "02")),
  stringCell rowSecondText.id [1, 1] "xx" (.rejected .declaredConstraint),
  stringCell rowSecondText.id [1, 2] "09" (.parsed (.str "09")),
  timeCell [1, 1] "12:34:56" (clock 12 34 56 (by decide)),
  timeCell [1, 2] "12:34:56" (clock 12 34 56 (by decide))]

private def earlierMissingStringOutcomes? : Option (List OutcomeSummary) := do
  let operation ← stringOperation?
  let input ← earlierMissingStringInput?
  let outcomes ← operation.execute input |>.toOption
  pure (outcomes.map summarizeOutcome)

/- Root, enclosing, and row-local Number components are admitted together at the repeatable target. -/
example : mixedOperation?.isSome = true := by
  native_decide

/- Constants and Number fields may share one prefix, retaining only the field dependencies in authored order. -/
example : constantFieldMix?.map (·.fieldDependencies) =
    some [rootHour.id, rowSecond.id] := by
  native_decide

/- String fields at root, enclosing-parent, and leaf scopes are admitted together, and may mix with Number fields and constants without losing authored dependency order. -/
example : stringOperation?.isSome = true ∧
    typedMix?.map (·.fieldDependencies) =
      some [rootHour.id, projectMinuteText.id] := by
  native_decide

/- Direct Time and DateTime extractors retain their root, enclosing-parent, and leaf scopes, and may mix with Number and String components without changing authored dependency order. -/
example : extractorOperation?.isSome = true ∧
    extractorMix?.map (·.fieldDependencies) =
      some [rootHour.id, projectMinuteText.id, rowStamp.id] := by
  native_decide

/- Extractor tokens are position-specific, and non-temporal sources fail at the source-kind gate. -/
example : staticError? (.hour (.extractor .minute
      (absolute ["Order"] "RootStamp"))) =
      some (.component (.extractorMismatch .hour .minute)) ∧
    staticError? (.hour (.extractor .hour
      (absolute ["Order"] "TextSource"))) =
      some (.component (.sourceKind .hour textSource.path .string)) := by
  native_decide

/- The String gate is independent of component position once placement is bound. -/
example : staticError? (.hour (.string
    (absolute ["Order", "Projects", "Tasks"] "RowSecondText"))) = none := by
  native_decide

/- The target cannot re-enter its own component prefix, even before the target's non-Number kind would be inspected. -/
example : staticError? (.hour (.number
    (absolute ["Order", "Projects", "Tasks"] "SelectedTime"))) =
    some (.component (.targetSelfReference target.id)) := by
  native_decide

/- A field-backed component keeps the exact scalar-kind gate. -/
example : staticError? (.hour (.number
    (absolute ["Order"] "TextSource"))) =
    some (.component (.sourceKind .hour textSource.path .string)) := by
  native_decide

/- A String component retains the same scalar-kind refusal before its declaration policy is inspected. -/
example : staticError? (.minute (.constant "0") (.string
    (absolute ["Order", "Projects"] "ProjectMinute"))) =
    some (.component (.sourceKind .minute projectMinute.path .number)) := by
  native_decide

/- A maximum-length-only String without a recognized digit pattern remains outside this component subset. -/
example : staticError? (.hour (.string
    (absolute ["Order"] "TextSource"))) =
    some (.component (.declarationNotAdmitted .hour textSource.path)) := by
  native_decide

/- A source in a sibling repetition tree is not bound by the target row environment. -/
example : staticError? (.hour (.number
    (absolute ["Order", "OtherRows"] "SiblingHour"))) =
    some (.component (.sourceScope target.path siblingHour.path)) := by
  native_decide

/- A Number declaration certified for minutes is not silently reused as an hour source. -/
example : staticError? (.hour (.number
    (absolute ["Order", "Projects"] "ProjectMinute"))) =
    some (.component (.declarationNotAdmitted .hour projectMinute.path)) := by
  native_decide

/- Each component reads at its own bound scope inside the current target row. Exact results preserve nested target identity, ordinary source equality, and retained-action application. -/
example : correlationResult? = some ({
    dependencies := [rootHour.id, projectMinute.id, rowSecond.id]
    successes := [
      (address target.id [1, 1], "05:02:09"),
      (address target.id [1, 2], "05:02:10"),
      (address target.id [2, 1], "05:04:09")
    ]
    changes := [
      (address target.id [1, 2], "05:02:10"),
      (address target.id [2, 1], "05:04:09")
    ]
    cleared := []
    applied := [
      (false, none),
      (true, some "05:02:10"),
      (true, some "05:04:09")
    ]
  } : CorrelationSummary) := by
  native_decide

/- Leading-zero String components convert to numeric clock parts while retaining each source's own repetition scope and the ordinary exact-address result/application partitions. -/
example : stringCorrelationResult? = some ({
    dependencies := [rootHourText.id, projectMinuteText.id, rowSecondText.id]
    successes := [
      (address target.id [1, 1], "05:02:09"),
      (address target.id [1, 2], "05:02:10"),
      (address target.id [2, 1], "05:04:09")
    ]
    changes := [
      (address target.id [1, 2], "05:02:10"),
      (address target.id [2, 1], "05:04:09")
    ]
    cleared := []
    applied := [
      (false, none),
      (true, some "05:02:10"),
      (true, some "05:04:09")
    ]
  } : CorrelationSummary) := by
  native_decide

/- Direct temporal extractors project typed clocks at their own bound scopes while preserving exact target identity, ordinary source equality, and retained-action application. -/
example : extractorCorrelationResult? = some ({
    dependencies := [rootStamp.id, projectTime.id, rowStamp.id]
    successes := [
      (address target.id [1, 1], "05:02:09"),
      (address target.id [1, 2], "05:02:10"),
      (address target.id [2, 1], "05:04:09")
    ]
    changes := [
      (address target.id [1, 2], "05:02:10"),
      (address target.id [2, 1], "05:04:09")
    ]
    cleared := []
    applied := [
      (false, none),
      (true, some "05:02:10"),
      (true, some "05:04:09")
    ]
  } : CorrelationSummary) := by
  native_decide

/- Missing parent and leaf components remain incomplete, formal invalidity remains poison, and only the clean row succeeds. Result application consumes all three retained clears before the one changed value. -/
example : missingResult? = some ({
    outcomes := [
      { target := address target.id [1, 1], value := none,
        noValue := true, poison := none },
      { target := address target.id [2, 1], value := none,
        noValue := true, poison := none },
      { target := address target.id [2, 2], value := none,
        noValue := false, poison := some .declaredConstraint },
      { target := address target.id [2, 3], value := some "05:02:09",
        noValue := false, poison := none }
    ]
    successes := [address target.id [2, 3]]
    changes := [address target.id [2, 3]]
    cleared := [
      address target.id [1, 1],
      address target.id [2, 1],
      address target.id [2, 2]
    ]
    residual := [.declaredConstraint]
    applied := [
      (true, none),
      (true, none),
      (true, none),
      (true, some "05:02:09")
    ]
  } : MissingSummary) := by
  native_decide

/- An earlier missing component does not hide a later reached formal failure; the clean sibling remains ordinary incomplete. -/
example : earlierMissingOutcomes? = some [
    { target := address target.id [1, 1], value := none,
      noValue := false, poison := some .declaredConstraint },
    { target := address target.id [1, 2], value := none,
      noValue := true, poison := none }
  ] := by
  native_decide

/- Missing String components stay incomplete, a reached pattern failure stays poison, and the clean sibling still succeeds. -/
example : stringFailureOutcomes? = some [
    { target := address target.id [1, 1], value := none,
      noValue := true, poison := none },
    { target := address target.id [2, 1], value := none,
      noValue := true, poison := none },
    { target := address target.id [2, 2], value := none,
      noValue := false, poison := some .declaredConstraint },
    { target := address target.id [2, 3], value := some "05:02:09",
      noValue := false, poison := none }
  ] := by
  native_decide

/- A two-digit String declaration does not impose a position maximum: `99` is statically valid input but yields an unreal clock, so only its source-filled target is cleared. -/
example : impossibleStringResult? = some ([
      { target := address target.id [1, 1], value := none,
        noValue := true, poison := none },
      { target := address target.id [1, 2], value := some "05:02:09",
        noValue := false, poison := none }
    ], [address target.id [1, 1]], [address target.id [1, 2]]) := by
  native_decide

/- An earlier missing String component does not hide a later reached pattern failure; a clean sibling remains ordinary incomplete. -/
example : earlierMissingStringOutcomes? = some [
    { target := address target.id [1, 1], value := none,
      noValue := false, poison := some .declaredConstraint },
    { target := address target.id [1, 2], value := none,
      noValue := true, poison := none }
  ] := by
  native_decide

/- Missing parent and leaf extractors remain incomplete, a reached malformed temporal source remains poison, and the clean sibling succeeds. -/
example : extractorFailureOutcomes? = some [
    { target := address target.id [1, 1], value := none,
      noValue := true, poison := none },
    { target := address target.id [2, 1], value := none,
      noValue := true, poison := none },
    { target := address target.id [2, 2], value := none,
      noValue := false, poison := some .dateFormat },
    { target := address target.id [2, 3], value := some "05:02:09",
      noValue := false, poison := none }
  ] := by
  native_decide

/- An earlier missing extractor does not hide a later reached formal failure; no physical target rows trigger any read. -/
example : earlierMissingExtractorOutcomes? = some [
      { target := address target.id [1, 1], value := none,
        noValue := false, poison := some .dateFormat },
      { target := address target.id [1, 2], value := none,
        noValue := true, poison := none }
    ] ∧ noTargetRowsExtractorOutcomes? = some [] := by
  native_decide

private def worldComponents : SurfaceAddressedWorldTimeComponents :=
  .second
    (.shiftedNowLiteral .hour .hours 0)
    (.addressed (.string
      (absolute ["Order", "Projects"] "ProjectMinuteText")))
    (.addressed (.extractor .second
      (absolute ["Order", "Projects", "Tasks"] "RowStamp")))

private def worldExpressionComponents : SurfaceAddressedWorldTimeComponents :=
  .second
    (.shiftedNowExpression ["Order"] .hour .hours
      (.binary .add
        (.atom (.field (absolute ["Order"] "RootHour")))
        (.atom (.field (absolute ["Order"] "RootHour")))))
    (.addressed (.string
      (absolute ["Order", "Projects"] "ProjectMinuteText")))
    (.addressed (.extractor .second
      (absolute ["Order", "Projects", "Tasks"] "RowStamp")))

private def worldRowShiftAmount : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add
    (.atom (.field (absolute ["Order", "Projects", "Tasks"] "RowSecond")))
    (.binary .add
      (.atom (.field (absolute ["Order"] "RootHour")))
      (.atom (.field (absolute ["Order", "Projects", "Tasks"] "RowSecond"))))

private def worldRowExpressionComponents : SurfaceAddressedWorldTimeComponents :=
  .second
    (.shiftedNowRowExpression .hour .hours worldRowShiftAmount)
    (.addressed (.string
      (absolute ["Order", "Projects"] "ProjectMinuteText")))
    (.addressed (.extractor .second
      (absolute ["Order", "Projects", "Tasks"] "RowStamp")))

private def worldOperation? (components := worldComponents) :
    Option (CheckedAddressedWorldTimeConstructionComputation model) :=
  (checkAddressedWorldTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id components).toOption

private def worldInput? (includeAmount := false) (includeRowAmounts := false) := document? [
    outerRow 1, outerRow 2,
    innerRow 1 1, innerRow 1 2, innerRow 2 1] (
  (if includeAmount then [numberCell rootHour.id [] 1] else []) ++
  (if includeRowAmounts then [
    numberCell rowSecond.id [1, 1] 1,
    numberCell rowSecond.id [1, 2] 2,
    numberCell rowSecond.id [2, 1] 3] else []) ++ [
    stringCell projectMinuteText.id [1] "02" (.parsed (.str "02")),
    stringCell projectMinuteText.id [2] "04" (.parsed (.str "04")),
    temporalCell rowStamp.id [1, 1] "2024-06-01T00:00:09"
      (dateTimeValue 0 0 9 (by decide)),
    temporalCell rowStamp.id [1, 2] "2024-06-01T00:00:10"
      (dateTimeValue 0 0 10 (by decide)),
    temporalCell rowStamp.id [2, 1] "2024-06-01T00:00:09"
      (dateTimeValue 0 0 9 (by decide)),
    timeCell [1, 1] "05:02:09" (clock 5 2 9 (by decide)),
    timeCell [1, 2] "12:34:56" (clock 12 34 56 (by decide))])

private def worldResult? (world : World)
    (components := worldComponents) (includeAmount := false)
    (includeRowAmounts := false) := do
  let operation ← worldOperation? components
  let input ← worldInput? includeAmount includeRowAmounts
  let view ← operation.executeResult world input ([] : List FormalCause) |>.toOption
  let destination ← emptyDestination?
  let applied ← view.applyToChecked destination |>.toOption
  pure (
    operation.fieldDependencies,
    view.time.withoutErrors.map fun (item : TimeComputedInstance CellAddr) =>
      (item.targetField, item.value.text),
    view.time.withChanges.map fun (item : TimeComputedInstance CellAddr) =>
      item.targetField,
    [[1, 1], [1, 2], [2, 1]].map fun path =>
      (applied (address target.id path)).storedValue.map StoredTemporalText.text)

/- The explicit world is sampled by the nested Hour component for every physical target row, while the enclosing String and leaf DateTime extractor retain their own scopes. A changed world changes every computed Hour without changing row identity. -/
example :
    worldResult? { now := { epochMillis := 18000000 } } = some (
      [projectMinuteText.id, rowStamp.id],
      [(address target.id [1, 1], "05:02:09"),
        (address target.id [1, 2], "05:02:10"),
        (address target.id [2, 1], "05:04:09")],
      [address target.id [1, 2], address target.id [2, 1]],
      [none, some "05:02:10", some "05:04:09"]) ∧
    (worldResult? { now := { epochMillis := 21600000 } }).map
      (fun result => result.2.1) = some [
        (address target.id [1, 1], "06:02:09"),
        (address target.id [1, 2], "06:02:10"),
        (address target.id [2, 1], "06:04:09")] := by
  native_decide

/- An addressed amount expression resolves leaf and outer Number atoms at each target row while retaining authored duplicates. -/
example :
    (worldOperation? worldRowExpressionComponents).map (·.fieldDependencies) =
      some [rowSecond.id, rootHour.id, rowSecond.id,
        projectMinuteText.id, rowStamp.id] ∧
    (worldResult? { now := { epochMillis := 18000000 } }
      worldRowExpressionComponents true true).map (fun result => result.2.1) = some [
        (address target.id [1, 1], "08:02:09"),
        (address target.id [1, 2], "10:02:10"),
        (address target.id [2, 1], "12:04:09")] := by
  native_decide

/- Row-local missing and formal amounts stay distinct, while no physical target row reaches the addressed expression. -/
example :
    (do
      let operation ← worldOperation? worldRowExpressionComponents
      let input ← document? [outerRow 1, innerRow 1 1, innerRow 1 2] [
        numberCell rootHour.id [] 1,
        rejectedNumberCell rowSecond.id [1, 2],
        stringCell projectMinuteText.id [1] "02" (.parsed (.str "02")),
        temporalCell rowStamp.id [1, 1] "2024-06-01T00:00:09"
          (dateTimeValue 0 0 9 (by decide)),
        temporalCell rowStamp.id [1, 2] "2024-06-01T00:00:10"
          (dateTimeValue 0 0 10 (by decide))]
      let outcomes ← operation.execute
        { now := { epochMillis := 18000000 } } input |>.toOption
      pure (outcomes.map summarizeOutcome)) = some [
          { target := address target.id [1, 1], value := none,
            noValue := true, poison := none },
          { target := address target.id [1, 2], value := none,
            noValue := false, poison := some .declaredConstraint }] ∧
    (do
      let operation ← worldOperation? worldRowExpressionComponents
      let input ← document? [] []
      operation.execute { now := { epochMillis := 18000000 } } input |>.toOption) =
        some [] := by
  native_decide

/- Computation-phase addressed expressions ignore a required-only finding just like their scalar amount sibling; validation still exposes it. -/
example :
    let requiredEmpty : CheckedCell := { rawPresent := false, parsed := none, findings := [.required] }
    let rootValue : CheckedCell := { rawPresent := true, parsed := some (.num 1), findings := [] }
    let document : Document := { instantiatedRows := [], rawCells := fun _ => none }
    let evaluate (phase : Phase) := do
      let amount ← (elaborateValueAsDateTimeRepeatableExpressionShiftAmount
        model ["Order", "Projects", "Tasks"] worldRowShiftAmount).toOption
      amount.readAddressed phase {
        scalar := {
          fields := { read := fun field =>
            if field == rootHour.id then rootValue else requiredEmpty }
          groups := GroupPresenceContext.unavailable
        }
        outer := [(10, 1), (20, 1)], input := .legacy document (fun _ _ => requiredEmpty)
      } |>.toOption
    (match evaluate .computation with
      | some (.ok (.value value .growOnly)) => value == 1
      | _ => false) &&
    (match evaluate .validation with
      | some (.error (.formal .required)) => true
      | _ => false) = true := by
  native_decide

/- A dynamic numeric amount remains the first authored dependency. -/
example :
    (worldOperation? worldExpressionComponents).map (·.fieldDependencies) =
      some [rootHour.id, rootHour.id, projectMinuteText.id, rowStamp.id] ∧
    (worldResult? { now := { epochMillis := 18000000 } }
      worldExpressionComponents true).map (fun result => result.2.1) = some [
        (address target.id [1, 1], "07:02:09"),
        (address target.id [1, 2], "07:02:10"),
        (address target.id [2, 1], "07:04:09")] := by
  native_decide

/- A wrong dynamic extractor token is refused at its own constructor position. -/
example :
    (match checkAddressedWorldTimeConstructionComputation model
        ["Order", "Projects", "Tasks"] target.id
        (.hour (.shiftedNowLiteral .minute .hours 0)) with
      | .error (.component (.shifted (.extractorMismatch .hour .minute))) => true
      | _ => false) = true := by
  native_decide

/- No physical target row reaches even a malformed dynamic shift amount. -/
example :
    (do
      let operation ← worldOperation? worldExpressionComponents
      let input ← document? [] [rejectedNumberCell rootHour.id []]
      operation.execute { now := { epochMillis := 18000000 } } input |>.toOption) =
        some [] := by
  native_decide

end A12Kernel.Conformance.AddressedTimeConstruction
