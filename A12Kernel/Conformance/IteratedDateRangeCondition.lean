import A12Kernel.Elaboration.ValidationRule

/-! # Iterated DateRange condition locks

These cases exercise the DateRange condition carriers that read a repeatable operand at the rule's
own row: stored equality, one selected endpoint against a fixed date, and two selected endpoints.

Their static verdicts are the Kernel rows in the rule-locus checkpoint. The same condition is
admitted when the rule iterates the operand's level and refused `MVK_NO_WILDCARD` when it does not,
and every comparison polarity is admitted from inside, which is what distinguishes a value
comparison from the negated presence predicates the iteration gate does refuse.

The runtime rows are internal compositions of two separately calibrated mechanisms — each carrier's
own verdict and the ordinary row scan. What is new here is only that the operand is read at the
iterating row rather than at the document root, which is exactly what the differing second row
separates.
-/

namespace A12Kernel.Conformance.IteratedDateRangeCondition

open A12Kernel

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "yyyy-MM-dd", separator := "/" }
}

private def existing := rangeField 1 ["Form"] "Existing"
private def rowRange := rangeField 2 ["Form", "Rows"] "RowRange" [10]
private def dotted : FlatFieldDecl := {
  rangeField 3 ["Form"] "Dotted" with
  dateRangePolicy := some { format := "dd.MM.yyyy", separator := "-" }
}
private def monthOnly : FlatFieldDecl := {
  rangeField 4 ["Form"] "MonthOnly" with
  dateRangePolicy := some { format := "MM", separator := "/" }
}

private def model : FlatModel := {
  fields := [existing, rowRange, dotted, monthOnly]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 5 }]
  timeZoneId := "UTC"
}

private def path (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def condition? (rowGroup : GroupPath) (left right : SurfaceFieldPath)
    (op : EqualityOp := .equal) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  CheckedValidationCondition.fromIteratedDateRangeEquality model rowGroup
    op left right

private def rowRangePath := path ["Form", "Rows"] "RowRange"
private def existingPath := path ["Form"] "Existing"

/- The locus decides admission. A rule iterating the operand's own level admits it in either
authored slot and under either equality direction, while the same condition read from the enclosing
scalar group is refused as a repeatable reference, which is the class that reports
`MVK_NO_WILDCARD`. -/
example :
    (condition? ["Form", "Rows"] rowRangePath existingPath).isOk = true ∧
      (condition? ["Form", "Rows"] existingPath rowRangePath).isOk = true ∧
      (condition? ["Form", "Rows"] rowRangePath existingPath .notEqual).isOk = true ∧
      (match condition? ["Form"] rowRangePath existingPath with
        | .error (.fieldReference (.repeatableReference path)) =>
            path == rowRange.path
        | _ => false) = true := by
  native_decide

/- A carrier with no repeatable operand belongs to the scalar owner, so this leaf refuses it rather
than offering a second way to express one condition. -/
example :
    (match condition? ["Form"] existingPath (path ["Form"] "Dotted") with
      | .error (.repeatableFieldRequired path) => path == existing.path
      | _ => false) = true := by
  native_decide

/- The operand gate is the declared component set, exactly as on the scalar carrier: the dotted
spelling of the same components crosses, and a month-only declaration does not. -/
example :
    (condition? ["Form", "Rows"] rowRangePath (path ["Form"] "Dotted")).isOk = true ∧
      (condition? ["Form", "Rows"] rowRangePath
        (path ["Form"] "MonthOnly")).isOk = false := by
  native_decide

/- The leaf contributes its operand's level to the rule's derived iteration scope, and it needs the
addressed evaluator, so a scalar route cannot silently read row one. -/
example :
    (match (condition? ["Form", "Rows"] rowRangePath existingPath).toOption with
      | some checked =>
          (match checked.core.ordinaryIterationScope with
            | .ok (some scope) => scope == [10]
            | _ => false) && checked.core.requiresAddressedValidation
      | none => false) = true := by
  native_decide

private def storedCell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw :=
    match model.lookupUniqueId field with
    | .ok declaration =>
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy =>
            (classifyStoredDateRangeForModel model.timeZoneId model.baseYear
              policy stored).toOption.getD .empty
        | none => .empty
    | .error _ => .empty
}

private def twoRowData : DocumentData := {
  instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
  cells := [
    storedCell existing.id [] "2024-06-01/2024-06-30",
    storedCell rowRange.id [1] "2024-06-01/2024-06-30",
    storedCell rowRange.id [2] "2024-07-01/2024-07-31"]
}

private def rowOutcomes? (op : EqualityOp) (data : DocumentData) :
    Option (List (Env × Verdict × Option MessagePointer)) := do
  let checked ← (condition? ["Form", "Rows"] rowRangePath existingPath op).toOption
  let rule ← (assembleResolvedValidationRule model checked rowRange.id
    "iteratedDateRangeEquality" .error { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun entry =>
    (entry.1, entry.2.verdict, entry.2.message?.map (·.errorAddress)))

private def rowVerdicts? (op : EqualityOp) (data : DocumentData) :
    Option (List (Env × Verdict)) :=
  (rowOutcomes? op data).map fun rows =>
    rows.map fun row => (row.1, row.2.1)

/- Each row is judged against its own cell rather than against row one: the matching row fires and
the differing row does not, in document order. -/
example :
    rowVerdicts? .equal twoRowData =
      some [([(10, 1)], .fired .value), ([(10, 2)], .notFired)] ∧
    rowVerdicts? .notEqual twoRowData =
      some [([(10, 1)], .notFired), ([(10, 2)], .fired .value)] := by
  native_decide

/- An empty operand leaves both directions unfired at the row that holds it, so the row scan does
not convert absence into a fired error. The scalar peer is filled in the same document, which is
what makes this an emptiness row rather than a missing-cell row. -/
example :
    rowVerdicts? .equal {
      instantiatedRows := [{ group := 10, path := [1] }]
      cells := [storedCell existing.id [] "2024-06-01/2024-06-30"] } =
      some [([(10, 1)], .notFired)] ∧
    rowVerdicts? .notEqual {
      instantiatedRows := [{ group := 10, path := [1] }]
      cells := [storedCell existing.id [] "2024-06-01/2024-06-30"] } =
      some [([(10, 1)], .notFired)] := by
  native_decide

/- The fired row reports on the error field at its own row, which is what an Explain consumer reads
off this leaf; the reference projection keeps both operands in authored order behind it. -/
example :
    (rowOutcomes? .equal twoRowData).map
        (fun rows => rows.map fun row => row.2.2) =
      some [some (MessagePointer.ofCellAddr
        { field := rowRange.id, path := [1] }), none] := by
  native_decide

/-! ## Selected endpoints read at the iterating row -/

private def june1 : FullDate :=
  (FullDate.ofYmd? 2024 6 1).get (by native_decide)

private def boundAgainstFixed? (rowGroup : GroupPath) (source : SurfaceFieldPath)
    (bound : DateRangeBound) (comparison : TemporalComparisonOp) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  CheckedValidationCondition.fromIteratedDateRangeBoundAgainstFixed model
    rowGroup source bound .left comparison june1

private def boundPair? (rowGroup : GroupPath)
    (left : SurfaceFieldPath) (leftBound : DateRangeBound)
    (right : SurfaceFieldPath) (rightBound : DateRangeBound)
    (comparison : TemporalComparisonOp) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  CheckedValidationCondition.fromIteratedDateRangeBoundPair model rowGroup
    left leftBound right rightBound comparison

/- Both endpoints and every order operator are admitted from inside the repeated group, and the same
conditions are refused as repeatable references from outside it. The locus, not the operator, is
what decides. -/
example :
    [boundAgainstFixed? ["Form", "Rows"] rowRangePath .start .equal,
      boundAgainstFixed? ["Form", "Rows"] rowRangePath .start .notEqual,
      boundAgainstFixed? ["Form", "Rows"] rowRangePath .start .before,
      boundAgainstFixed? ["Form", "Rows"] rowRangePath .finish .afterOrEqual].all
        (·.isOk) = true ∧
      (match boundAgainstFixed? ["Form"] rowRangePath .start .equal with
        | .error (.fieldReference (.repeatableReference path)) =>
            path == rowRange.path
        | _ => false) = true := by
  native_decide

/- The pair admits a repeatable endpoint against a scalar peer and two endpoints of the same
repeatable row, and is refused from outside the group. A month-only peer is refused by the ordinary
comparability rule rather than by anything this carrier adds. -/
example :
    (boundPair? ["Form", "Rows"] rowRangePath .start existingPath .finish
        .before).isOk = true ∧
      (boundPair? ["Form", "Rows"] rowRangePath .start rowRangePath .finish
        .before).isOk = true ∧
      (boundPair? ["Form"] rowRangePath .start existingPath .finish
        .before).isOk = false ∧
      (boundPair? ["Form", "Rows"] rowRangePath .start
        (path ["Form"] "MonthOnly") .finish .before).isOk = false := by
  native_decide

private def endpointRowVerdicts? (condition :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model))
    (data : DocumentData) : Option (List (Env × Verdict)) := do
  let checked ← condition.toOption
  let rule ← (assembleResolvedValidationRule model checked rowRange.id
    "iteratedDateRangeEndpoint" .error { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun entry => (entry.1, entry.2.verdict))

/- The endpoint is selected from each row's own value: row one starts on the fixed date and row two
does not, and the finish endpoint of the same rows separates the two selections. -/
example :
    endpointRowVerdicts?
        (boundAgainstFixed? ["Form", "Rows"] rowRangePath .start .equal)
        twoRowData =
      some [([(10, 1)], .fired .value), ([(10, 2)], .notFired)] ∧
    endpointRowVerdicts?
        (boundAgainstFixed? ["Form", "Rows"] rowRangePath .finish .equal)
        twoRowData =
      some [([(10, 1)], .notFired), ([(10, 2)], .notFired)] := by
  native_decide

/- The pair compares two endpoints of one row, so a well-ordered row does not fire while its own
start and finish are read from the same cell. -/
example :
    endpointRowVerdicts?
        (boundPair? ["Form", "Rows"] rowRangePath .finish rowRangePath .start
          .before) twoRowData =
      some [([(10, 1)], .notFired), ([(10, 2)], .notFired)] ∧
    endpointRowVerdicts?
        (boundPair? ["Form", "Rows"] rowRangePath .start rowRangePath .finish
          .before) twoRowData =
      some [([(10, 1)], .fired .value), ([(10, 2)], .fired .value)] := by
  native_decide

end A12Kernel.Conformance.IteratedDateRangeCondition
