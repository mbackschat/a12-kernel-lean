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

/-! ## The overlap predicate at an iterating row -/

private def operand (groups : List String) (field : String) :
    SurfaceFieldEntityOperand :=
  .field { base := .absolute, groups, field }

private def rowsStar (field : String) : SurfaceFieldEntityOperand :=
  .star {
    base := .absolute
    groups := [{ name := "Form" }, { name := "Rows", starred := true }]
    field
  }

private def overlap? (rowGroup : GroupPath) (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  CheckedValidationCondition.fromIteratedDateRangeOverlap model rowGroup
    { first, rest }

private def bareRow := operand ["Form", "Rows"] "RowRange"
private def scalarExisting := operand ["Form"] "Existing"
private def scalarDotted := operand ["Form"] "Dotted"

/- The locus decides the bare operand here exactly as it does on the comparison carriers, in either
slot, at list length three, and beside a starred occurrence of the same field — the mixed spelling
the Kernel admits from this locus. Read from the enclosing scalar group the same condition is
refused as a repeatable reference. -/
example :
    [overlap? ["Form", "Rows"] bareRow [scalarExisting],
      overlap? ["Form", "Rows"] scalarExisting [bareRow],
      overlap? ["Form", "Rows"] bareRow [scalarExisting, scalarDotted],
      overlap? ["Form", "Rows"] bareRow [rowsStar "RowRange"]].all (·.isOk) =
      true ∧
    (match overlap? ["Form"] bareRow [scalarExisting] with
      | .error (.fieldReference (.repeatableReference path)) =>
          path == rowRange.path
      | _ => false) = true := by
  native_decide

/- A list whose only repeatable reference is a **star** reads no enclosing row, so it stays with the
scalar overlap owner rather than becoming a second way to express one condition. This leaf refuses
it from either locus, and the refusal names the operand it would have had to read. -/
example :
    (match overlap? ["Form", "Rows"] (rowsStar "RowRange") [scalarExisting] with
      | .error (.repeatableFieldRequired path) => path == existing.path
      | _ => false) = true ∧
    (match overlap? ["Form"] (rowsStar "RowRange") [scalarExisting] with
      | .error (.repeatableFieldRequired path) => path == existing.path
      | _ => false) = true := by
  native_decide

/- Every whole-list gate stays the scalar operator's: a sole operand is still refused for
multiplicity, a repeated operand for duplication, and a group operand outright. Only the operand
locus widened. -/
example :
    (overlap? ["Form", "Rows"] bareRow []).isOk = false ∧
      (overlap? ["Form", "Rows"] bareRow [bareRow]).isOk = false ∧
      (overlap? ["Form", "Rows"] bareRow
        [.group (.path { base := .absolute, groups := ["Form", "Rows"] })]).isOk =
        false := by
  native_decide

/- The bare operand contributes its level to the derived iteration scope and the leaf needs the
addressed evaluator. A starred operand beside it adds nothing to that scope, because a star reopens
its own level rather than reading the enclosing row. -/
example :
    (match (overlap? ["Form", "Rows"] bareRow [scalarExisting]).toOption with
      | some checked =>
          (match checked.core.ordinaryIterationScope with
            | .ok (some scope) => scope == [10]
            | _ => false) && checked.core.requiresAddressedValidation
      | none => false) = true ∧
    (match (overlap? ["Form", "Rows"] bareRow [rowsStar "RowRange"]).toOption with
      | some checked =>
          (match checked.core.ordinaryIterationScope with
            | .ok (some scope) => scope == [10]
            | _ => false)
      | none => false) = true := by
  native_decide

private def overlapRowVerdicts? (rowGroup : GroupPath)
    (first : SurfaceFieldEntityOperand) (rest : List SurfaceFieldEntityOperand)
    (data : DocumentData) : Option (List (Env × Verdict)) := do
  let checked ← (overlap? rowGroup first rest).toOption
  let rule ← (assembleResolvedValidationRule model checked rowRange.id
    "iteratedDateRangeOverlap" .error { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun entry => (entry.1, entry.2.verdict))

private def overlapData : DocumentData := {
  instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
  cells := [
    storedCell existing.id [] "2024-06-15/2024-07-15",
    storedCell rowRange.id [1] "2024-06-01/2024-06-30",
    storedCell rowRange.id [2] "2024-01-01/2024-01-31"]
}

/- Each row is scanned against its own value: the row whose window meets the scalar range fires and
the row that does not stay unfired, which is what separates the row read from a root read. -/
example :
    overlapRowVerdicts? ["Form", "Rows"] bareRow [scalarExisting] overlapData =
      some [([(10, 1)], .fired .value), ([(10, 2)], .notFired)] := by
  native_decide

/- The mixed spelling composes the two reads rather than choosing between them: the bare operand
contributes the current row and the star contributes every row, so the current row forms a same-cell
self-pair and the predicate fires on every row that has a value. That is the canonical clause's own
account of a scalar-plus-star list, now reached from an iterating locus; the admission is measured
and the verdict is this composition, which is locked because a consumer expecting the star to exclude
the current row would read the opposite outcome. -/
example :
    overlapRowVerdicts? ["Form", "Rows"] bareRow [rowsStar "RowRange"]
        overlapData =
      some [([(10, 1)], .fired .value), ([(10, 2)], .fired .value)] := by
  native_decide

/- A row with no stored range skips its slot, so the scan cannot fire on absence. -/
example :
    overlapRowVerdicts? ["Form", "Rows"] bareRow [scalarExisting] {
      instantiatedRows := [{ group := 10, path := [1] }]
      cells := [storedCell existing.id [] "2024-06-15/2024-07-15"] } =
      some [([(10, 1)], .notFired)] := by
  native_decide

/-! ## A constructed range compared with a stored range at the iterating row -/

private def dateField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel := []) : FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format := "yyyy-MM-dd", partialMode := .full }
}

private def rowStart := dateField 5 ["Form", "Rows"] "RowStart" [10]
private def rowFinish := dateField 6 ["Form", "Rows"] "RowFinish" [10]
private def scalarStart := dateField 7 ["Form"] "ScalarStart"
private def scalarFinish := dateField 8 ["Form"] "ScalarFinish"

private def constructionModel : FlatModel := {
  model with
  fields := model.fields ++ [rowStart, rowFinish, scalarStart, scalarFinish]
}

private def construction? (rowGroup : GroupPath)
    (start finish stored : SurfaceFieldPath)
    (position : DateRangeConstructionPosition := .right) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition constructionModel) :=
  CheckedValidationCondition.fromIteratedDateRangeConstructionAgainstStored
    constructionModel rowGroup start finish stored position .equal

private def rowStartPath := path ["Form", "Rows"] "RowStart"
private def rowFinishPath := path ["Form", "Rows"] "RowFinish"

/- The construction's endpoints obey the same locus rule as a stored operand: repeatable endpoints
against a scalar stored range are admitted from inside and refused from outside, in either authored
position, and the refusal names the endpoint it could not read. -/
example :
    (construction? ["Form", "Rows"] rowStartPath rowFinishPath
        existingPath).isOk = true ∧
      (construction? ["Form", "Rows"] rowStartPath rowFinishPath existingPath
        .left).isOk = true ∧
      (match construction? ["Form"] rowStartPath rowFinishPath existingPath with
        | .error (.fieldReference (.repeatableReference path)) =>
            path == rowStart.path
        | _ => false) = true := by
  native_decide

/- A repeatable stored operand beside scalar endpoints is admitted too, so either half may be the
one the rule iterates; and an all-scalar condition belongs to the existing mixed carrier rather than
this leaf. -/
example :
    (construction? ["Form", "Rows"] (path ["Form"] "ScalarStart")
        (path ["Form"] "ScalarFinish") rowRangePath).isOk = true ∧
      (match construction? ["Form"] (path ["Form"] "ScalarStart")
          (path ["Form"] "ScalarFinish") existingPath with
        | .error (.repeatableFieldRequired path) => path == scalarStart.path
        | _ => false) = true := by
  native_decide

private def constructionRowVerdicts? (start finish stored : SurfaceFieldPath)
    (data : DocumentData) : Option (List (Env × Verdict)) := do
  let checked ← (construction? ["Form", "Rows"] start finish stored).toOption
  let rule ← (assembleResolvedValidationRule constructionModel checked
    rowStart.id "iteratedConstruction" .error { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler constructionModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun entry => (entry.1, entry.2.verdict))

private def dateValue (epochMillis : Int) (year : Int)
    (month day : Nat) : DateValue :=
  { instant := { epochMillis }, parts := { year, month, day }
    basis := .storedGregorian }

private def constructionCell (field : FieldId) (path : List Nat)
    (stored : String) (value : DateValue) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw := .parsed (.temporal (.date value))
}

private def june1Value := dateValue 1717200000000 2024 6 1
private def june30Value := dateValue 1719705600000 2024 6 30
private def july31Value := dateValue 1722384000000 2024 7 31

/- Each row constructs from its own endpoints: the row whose endpoints reproduce the stored range
fires, and the row whose finish endpoint differs does not. -/
example :
    constructionRowVerdicts? rowStartPath rowFinishPath existingPath {
      instantiatedRows := [
        { group := 10, path := [1] }, { group := 10, path := [2] }]
      cells := [
        storedCell existing.id [] "2024-06-01/2024-06-30",
        constructionCell rowStart.id [1] "2024-06-01" june1Value,
        constructionCell rowFinish.id [1] "2024-06-30" june30Value,
        constructionCell rowStart.id [2] "2024-06-01" june1Value,
        constructionCell rowFinish.id [2] "2024-07-31" july31Value] } =
      some [([(10, 1)], .fired .value), ([(10, 2)], .notFired)] := by
  native_decide

/-! ## The plural overlap predicate at an iterating row -/

private def plural? (rowGroup : GroupPath) (scalar : SurfaceFieldEntityOperand)
    (first : SurfaceFieldEntityOperand)
    (rest : List SurfaceFieldEntityOperand := []) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  CheckedValidationCondition.fromIteratedDateRangePluralOverlap model rowGroup
    { scalar, list := { first, rest } }

/- Either side may be the one the rule iterates, and both are refused from the enclosing scalar
group. A starred list operand is locus-free and needs no row read, so a list of stars beside a scalar
belongs to the scalar owner and is refused here. -/
example :
    (plural? ["Form", "Rows"] bareRow scalarExisting).isOk = true ∧
      (plural? ["Form", "Rows"] scalarExisting bareRow).isOk = true ∧
      (match plural? ["Form"] bareRow scalarExisting with
        | .error (.fieldReference (.repeatableReference path)) =>
            path == rowRange.path
        | _ => false) = true ∧
      (match plural? ["Form"] scalarExisting bareRow with
        | .error (.fieldReference (.repeatableReference path)) =>
            path == rowRange.path
        | _ => false) = true ∧
      (match plural? ["Form", "Rows"] scalarExisting (rowsStar "RowRange") with
        | .error (.repeatableFieldRequired path) => path == existing.path
        | _ => false) = true := by
  native_decide

/- The locus widening adds no admission of its own. The cross-side duplicate check still refuses one
operand named on both sides, while the two declared spellings of one component set still cross, since
this operator applies no component gate. -/
example :
    (plural? ["Form", "Rows"] bareRow bareRow).isOk = false ∧
      (plural? ["Form", "Rows"] bareRow scalarDotted).isOk = true := by
  native_decide

private def pluralRowVerdicts? (scalar : SurfaceFieldEntityOperand)
    (first : SurfaceFieldEntityOperand) (data : DocumentData) :
    Option (List (Env × Verdict)) := do
  let checked ← (plural? ["Form", "Rows"] scalar first).toOption
  let rule ← (assembleResolvedValidationRule model checked rowRange.id
    "iteratedPluralOverlap" .error { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun entry => (entry.1, entry.2.verdict))

/- The scalar-versus-list scan runs per row: the row whose range meets the scalar list member fires
and the row that does not stay unfired, in either authored arrangement. -/
example :
    pluralRowVerdicts? bareRow scalarExisting overlapData =
      some [([(10, 1)], .fired .value), ([(10, 2)], .notFired)] ∧
    pluralRowVerdicts? scalarExisting bareRow overlapData =
      some [([(10, 1)], .fired .value), ([(10, 2)], .notFired)] := by
  native_decide

/- An unusable scalar terminates before the list is read, so a row with no stored range does not
fire even though its scalar peer is filled. -/
example :
    pluralRowVerdicts? bareRow scalarExisting {
      instantiatedRows := [{ group := 10, path := [1] }]
      cells := [storedCell existing.id [] "2024-06-15/2024-07-15"] } =
      some [([(10, 1)], .notFired)] := by
  native_decide

end A12Kernel.Conformance.IteratedDateRangeCondition
