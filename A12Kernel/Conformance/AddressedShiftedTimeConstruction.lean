import A12Kernel.Elaboration.AddressedWorldTimeConstruction

/-! # Repeatable field-shifted `Time(...)` construction locks -/

namespace A12Kernel.Conformance.AddressedShiftedTimeConstruction

open A12Kernel

private def numberField (id : FieldId) (name : String)
    (groupPath : GroupPath) (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, name, groupPath, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := false } }
}

private def rootAmount := numberField 1 "RootAmount" ["Order"] []
private def rowAmount :=
  numberField 2 "RowAmount" ["Order", "Projects", "Tasks"] [10, 20]

private def source : FlatFieldDecl := {
  id := 3
  name := "ProjectStamp"
  groupPath := ["Order", "Projects"]
  repeatableScope := [10]
  policy := { kind := .temporal .dateTime TemporalComponents.now }
  temporalTargetPolicy := some { format := "yyyy-MM-dd'T'HH:mm:ss" }
}

private def target : FlatFieldDecl := {
  id := 4
  name := "SelectedTime"
  groupPath := ["Order", "Projects", "Tasks"]
  repeatableScope := [10, 20]
  policy := { kind := .temporal .time TemporalComponents.time }
  temporalTargetPolicy := some { format := "HH:mm:ss" }
}

private def model : FlatModel := {
  fields := [rootAmount, rowAmount, source, target]
  repeatableGroups := [
    { level := 10, path := ["Order", "Projects"], repeatability := some 3 },
    { level := 20, path := ["Order", "Projects", "Tasks"], repeatability := some 3 }
  ]
  timeZoneId := "UTC"
}

private def absolute (groups : GroupPath) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def shiftAmount : AuthoredNumericExpr SurfaceNumericAtom :=
  .binary .add
    (.atom (.field (absolute ["Order", "Projects", "Tasks"] "RowAmount")))
    (.binary .add
      (.atom (.field (absolute ["Order"] "RootAmount")))
      (.atom (.field (absolute ["Order", "Projects", "Tasks"] "RowAmount"))))

private def components : SurfaceAddressedWorldTimeComponents :=
  .second
    (.shiftedDateTimeRowExpression
      (absolute ["Order", "Projects"] "ProjectStamp")
      .hour .hours shiftAmount)
    (.addressed (.constant "2"))
    (.addressed (.constant "9"))

private def operation? :=
  (checkAddressedWorldTimeConstructionComputation model
    ["Order", "Projects", "Tasks"] target.id components).toOption

private def row (group : RepeatableLevel) (path : List Nat) : RowAddr :=
  { group, path }

private def cell (field : FieldId) (path : List Nat)
    (stored : String) (raw : RawCell) : ClassifiedCellInput :=
  { address := { field, path }, stored, raw }

private def numberCell (field : FieldId) (path : List Nat) (value : Rat) :=
  cell field path (toString value) (.parsed (.num value))

private def clock (hour minute second : Nat)
    (valid : hour < 24 ∧ minute < 60 ∧ second < 60) : TimeOfDay :=
  ⟨hour, minute, second, valid⟩

private def dateTimeCell (path : List Nat) (hour : Nat) (valid : hour < 24) :=
  cell source.id path "stamp" (.parsed (.temporal (.dateTime
    { epochMillis := hour * 3600000 }
    { year := 1970, month := 1, day := 1 }
    (clock hour 0 0 ⟨valid, by decide, by decide⟩) .storedGregorian)))

private def prepared : PreparedFlatStringContext model
    builtinStringPatternCompiler :=
  (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption.get (by native_decide)

private def document? (rows : List RowAddr)
    (cells : List ClassifiedCellInput) : Option (CheckedDocument model) :=
  (checkDocument prepared "en_US" { instantiatedRows := rows, cells }).toOption

private def rows := [
  row 10 [1], row 10 [2],
  row 20 [1, 1], row 20 [1, 2], row 20 [2, 1]]

private def input? := document? rows [
  numberCell rootAmount.id [] 1,
  numberCell rowAmount.id [1, 1] 1,
  numberCell rowAmount.id [1, 2] 2,
  numberCell rowAmount.id [2, 1] 3,
  dateTimeCell [1] 5 (by decide),
  dateTimeCell [2] 10 (by decide)]

private structure Summary where
  path : List Nat
  value : Option String
  noValue : Bool
  poison : Option FormalCause
  deriving Repr, DecidableEq

private def summarize (outcome : AddressedTimeConstructionOutcome) : Summary := {
  path := outcome.targetField.path
  value := match outcome.outcome with
    | .accepted value => some value.text
    | .noValue | .poison _ => none
  noValue := match outcome.outcome with
    | .noValue => true
    | .accepted _ | .poison _ => false
  poison := match outcome.outcome with
    | .poison cause => some cause
    | .accepted _ | .noValue => none
  }

/- The shifted source precedes every amount atom in authored dependency order, and each target row binds the enclosing source plus its own row amount. -/
example :
    operation?.map (fun operation => operation.fieldDependencies) =
      some [source.id, rowAmount.id, rootAmount.id, rowAmount.id] ∧
    (do
      let operation ← operation?
      let input ← input?
      let outcomes ← operation.execute { now := { epochMillis := 0 } } input
        |>.toOption
      pure (outcomes.map summarize)) = some [
        { path := [1, 1], value := some "08:02:09",
          noValue := false, poison := none },
        { path := [1, 2], value := some "10:02:09",
          noValue := false, poison := none },
        { path := [2, 1], value := some "17:02:09",
          noValue := false, poison := none }] := by
  native_decide

/- Analyze retains both the nested temporal source and every distinct Number amount field. -/
example :
    operation?.map (fun operation =>
      (operation.referencesField source.id,
        operation.referencesField rowAmount.id,
        operation.referencesField rootAmount.id,
        operation.referencesField target.id)) =
      some (true, true, true, false) := by
  native_decide

/- A formal DateTime source hides its malformed amount, while an empty source reaches the same amount and exposes that distinct cause. -/
example :
    (do
      let operation ← operation?
      let input ← document? [
          row 10 [1], row 10 [2], row 20 [1, 1], row 20 [2, 1]] [
        numberCell rootAmount.id [] 1,
        cell rowAmount.id [1, 1] "bad" (.rejected .malformed),
        cell rowAmount.id [2, 1] "bad" (.rejected .malformed),
        cell source.id [1] "bad" (.rejected .dateFormat)]
      let outcomes ← operation.execute { now := { epochMillis := 0 } } input
        |>.toOption
      pure (outcomes.map summarize)) = some [
        { path := [1, 1], value := none,
          noValue := false, poison := some .dateFormat },
        { path := [2, 1], value := none,
          noValue := false, poison := some .malformed }] := by
  native_decide

/- No physical target row reaches either the stored source or the addressed amount. -/
example :
    (do
      let operation ← operation?
      let input ← document? [] [
        cell rootAmount.id [] "bad" (.rejected .malformed)]
      operation.execute { now := { epochMillis := 0 } } input |>.toOption) =
        some [] := by
  native_decide

/- The extractor token remains position-specific before any source is read. -/
example :
    (match checkAddressedWorldTimeConstructionComputation model
        ["Order", "Projects", "Tasks"] target.id
        (.hour (.shiftedDateTimeRowExpression
          (absolute ["Order", "Projects"] "ProjectStamp")
          .minute .hours shiftAmount)) with
      | .error (.component (.shifted (.extractorMismatch .hour .minute))) => true
      | _ => false) = true := by
  native_decide

end A12Kernel.Conformance.AddressedShiftedTimeConstruction
