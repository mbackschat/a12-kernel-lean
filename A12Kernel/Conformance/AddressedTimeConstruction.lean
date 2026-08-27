import A12Kernel.Elaboration.TimeComputation

/-! # Repeatable field-backed `Time(...)` construction locks -/

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
    rootHourText, projectMinuteText, rowSecondText]
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

private def typedMix? :
    Option (CheckedAddressedTimeConstructionComputation model) :=
  (checkAddressedTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id
    (.second
      (.number (absolute ["Order"] "RootHour"))
      (.string (absolute ["Order", "Projects"] "ProjectMinuteText"))
      (.constant "9")))
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

end A12Kernel.Conformance.AddressedTimeConstruction
