import A12Kernel.Elaboration.ValidationRule

/-! # Iterated unconfigured yearless DateRange condition locks

These cases exercise the DateRange condition carriers whose **value domain** is a retained yearless
label rather than a resolved date, read at the rule's own row. The model declares no Base Year, so
nothing completes a label into a range.

Their static verdicts are the Kernel rows in the yearless-locus checkpoint. The locus rule reaches
these carriers unchanged, and the separate refusal of a yearless endpoint against a complete date
literal fires from inside the repeated group too, which is what keeps the two gates distinguishable.
-/

namespace A12Kernel.Conformance.IteratedYearlessDateRangeCondition

open A12Kernel

/-! ## An unconfigured yearless endpoint pair at the iterating row -/

private def path (groups : List String) (field : String) : SurfaceFieldPath :=
  { base := .absolute, groups, field }

private def yearlessRange (id : FieldId) (groupPath : GroupPath)
    (name : String) (scope : List RepeatableLevel := []) : FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format := "MM", separator := "/" }
}

private def rowMonths := yearlessRange 9 ["Form", "Rows"] "RowMonths" [10]
private def scalarMonths := yearlessRange 10 ["Form"] "ScalarMonths"

/-- No Base Year, so a yearless declaration stays a retained label pair rather than being
completed into an exact range. -/
private def yearlessModel : FlatModel := {
  fields := [rowMonths, scalarMonths]
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 5 }]
  timeZoneId := "UTC"
}

private def yearlessPair? (rowGroup : GroupPath)
    (left : SurfaceFieldPath) (leftBound : DateRangeBound)
    (right : SurfaceFieldPath) (rightBound : DateRangeBound)
    (comparison : TemporalComparisonOp := .equal) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition yearlessModel) :=
  CheckedValidationCondition.fromIteratedDateRangeBoundPair yearlessModel
    rowGroup left leftBound right rightBound comparison

private def rowMonthsPath := path ["Form", "Rows"] "RowMonths"
private def scalarMonthsPath := path ["Form"] "ScalarMonths"

/- An unconfigured yearless endpoint reaches the same locus rule as an exact one: admitted from
inside the repeated group, refused from outside it. The pair lands in the yearless domain because
the exact owner refuses the policy, which is the same preference order the scalar carrier uses. -/
example :
    (yearlessPair? ["Form", "Rows"] rowMonthsPath .start scalarMonthsPath
        .start).isOk = true ∧
      (yearlessPair? ["Form", "Rows"] rowMonthsPath .finish scalarMonthsPath
        .finish .before).isOk = true ∧
      (match yearlessPair? ["Form"] rowMonthsPath .start scalarMonthsPath
          .start with
        | .error (.fieldReference (.repeatableReference path)) =>
            path == rowMonths.path
        | _ => false) = true := by
  native_decide

private def yearlessCell (field : FieldId) (path : List Nat)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path }
  stored
  raw :=
    match yearlessModel.lookupUniqueId field with
    | .ok declaration =>
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy =>
            (classifyStoredDateRangeForModel yearlessModel.timeZoneId
              yearlessModel.baseYear policy stored).toOption.getD .empty
        | none => .empty
    | .error _ => .empty
}

private def yearlessRowVerdicts? (leftBound rightBound : DateRangeBound)
    (data : DocumentData) : Option (List (Env × Verdict)) := do
  let checked ← (yearlessPair? ["Form", "Rows"] rowMonthsPath leftBound
    scalarMonthsPath rightBound).toOption
  let rule ← (assembleResolvedValidationRule yearlessModel checked rowMonths.id
    "iteratedYearlessPair" .error { parts := [] }).toOption
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler yearlessModel).toOption
  let document ← (checkDocument prepared "en_US" data).toOption
  let outcomes ← (rule.evalOrdinaryRepeatableFull document).toOption
  pure (outcomes.map fun entry => (entry.1, entry.2.verdict))

private def yearlessData : DocumentData := {
  instantiatedRows := [{ group := 10, path := [1] }, { group := 10, path := [2] }]
  cells := [
    yearlessCell scalarMonths.id [] "06/09",
    yearlessCell rowMonths.id [1] "06/09",
    yearlessCell rowMonths.id [2] "07/09"]
}

/- Each row compares its own retained labels: the matching start label fires and the differing one
does not, with the label completion by authored position supplied by the shared yearless owner. -/
example :
    yearlessRowVerdicts? .start .start yearlessData =
      some [([(10, 1)], .fired .value), ([(10, 2)], .notFired)] ∧
    yearlessRowVerdicts? .finish .finish yearlessData =
      some [([(10, 1)], .fired .value), ([(10, 2)], .fired .value)] := by
  native_decide

end A12Kernel.Conformance.IteratedYearlessDateRangeCondition
