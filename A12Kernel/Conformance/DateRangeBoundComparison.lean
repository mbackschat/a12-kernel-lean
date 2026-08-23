import A12Kernel.Elaboration.DateRangeBoundComparison

/-! # Endpoint-pair comparison locks

These cases run the whole route for a model with no Base Year: which endpoint pairs the
ordinary temporal admission rule accepts, which it refuses, and how a completed yearless label
decides the verdict. The admission verdicts and the filled comparison rows are the Kernel rows
in the unconfigured-bound checkpoint, decided and observed on both codegen strategies. The
empty rows are internal compositions of the shared empty projection.
-/

namespace A12Kernel.Conformance.DateRangeBoundComparison

open A12Kernel

private def rangeField (id : FieldId) (name format separator : String) :
    FlatFieldDecl := {
  id, name, groupPath := ["Form"]
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
}

private def model : FlatModel := {
  fields := [
    rangeField 1 "MonthSlash" "MM" "/",
    rangeField 2 "MonthEmpty" "MM" "",
    rangeField 3 "MonthDaySlash" "MM-dd" "/",
    rangeField 4 "YearA" "yyyy" "/",
    rangeField 5 "YearMonthA" "yyyy-MM" "/",
    rangeField 6 "IsoA" "yyyy-MM-dd" "/"]
  timeZoneId := "UTC"
}

private def pairError? (left : FieldId) (leftBound : DateRangeBound)
    (right : FieldId) (rightBound : DateRangeBound)
    (comparison : TemporalComparisonOp) :
    Option DateRangeBoundPairElabError :=
  match elaborateDateRangeBoundPair model left leftBound right rightBound
      comparison with
  | .ok _ => none
  | .error error => some error

private def pairAdmitted (left : FieldId) (right : FieldId)
    (comparison : TemporalComparisonOp := .equal) : Bool :=
  (pairError? left .start right .start comparison).isNone

/- The pair gate is the ordinary direct temporal rule, so it reads year presence rather than
requiring identical component sets: two yearless endpoints cross their component sets freely
under equality, inequality, and ordering, and so do two year-bearing ones. -/
example :
    [pairAdmitted 1 2, pairAdmitted 1 3, pairAdmitted 3 1,
      pairAdmitted 1 2 .notEqual, pairAdmitted 1 3 .before,
      pairAdmitted 1 2 .beforeOrEqual,
      pairAdmitted 6 5, pairAdmitted 6 4 .before, pairAdmitted 4 5] =
      List.replicate 9 true := by
  native_decide

/- A yearless endpoint against a year-bearing one is refused with the Kernel's compare
diagnostic, because no Base Year supplies the missing year. The refusal names both component
sets, so a consumer learns which side to change. -/
example :
    pairError? 1 .start 4 .start .equal =
        some (.formatsNotComparable
          (DateRangeInputFormat.yearlessMonth.components)
          (DateRangeInputFormat.yearFragment.components)) ∧
      (pairError? 1 .start 4 .start .equal).bind
        DateRangeBoundPairElabError.diagnostic? =
      some .invalidCompareToDate ∧
    (pairError? 3 .start 6 .start .before).isSome = true ∧
    KernelStaticDiagnostic.invalidCompareToDate.kernelCode =
      "MVK_INVALID_COMPARE_TO_DATE" := by
  native_decide

/-- Classify one stored token exactly as the checked-document route does, so the fixture cannot
disagree with canonical classification. -/
private def storedCell (field : FieldId) (stored : String) : ClassifiedCellInput := {
  address := { field, path := [] }
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

private def pairResult? (left : FieldId) (leftBound : DateRangeBound)
    (right : FieldId) (rightBound : DateRangeBound)
    (comparison : TemporalComparisonOp)
    (cells : List ClassifiedCellInput) : Option DateRangeBoundPairResult := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ← (elaborateDateRangeBoundPair model left leftBound right rightBound
    comparison).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  }).toOption
  (checked.evaluate document).toOption

private def pairVerdict? (left : FieldId) (leftBound : DateRangeBound)
    (right : FieldId) (rightBound : DateRangeBound)
    (comparison : TemporalComparisonOp)
    (cells : List ClassifiedCellInput) : Option Verdict :=
  (pairResult? left leftBound right rightBound comparison cells).map fun
    | .exact _ _ verdict => verdict
    | .yearless _ _ verdict => verdict

private def juneToSeptember : List ClassifiedCellInput :=
  [storedCell 1 "06/09", storedCell 2 "0609", storedCell 3 "06-01/09-30"]

private def juneSecondToSeptemberTwentyNinth : List ClassifiedCellInput :=
  [storedCell 1 "06/09", storedCell 3 "06-02/09-29"]

/- A month-only start completes to the first day, so it equals a month-and-day start exactly
when that day is the first, and is strictly earlier when the day is later. Nothing manufactures
a year: the labels are compared as labels. -/
example :
    pairVerdict? 1 .start 3 .start .equal juneToSeptember =
        some (.fired .value) ∧
      pairVerdict? 1 .start 3 .start .equal
        juneSecondToSeptemberTwentyNinth = some .notFired ∧
      pairVerdict? 1 .start 3 .start .before
        juneSecondToSeptemberTwentyNinth = some (.fired .value) ∧
      pairVerdict? 1 .start 2 .start .equal juneToSeptember =
        some (.fired .value) := by
  native_decide

/- A month-only finish completes to the greatest day its month can ever have, which is why a
September finish equals day 30 and not day 29. -/
example :
    pairVerdict? 1 .finish 3 .finish .equal juneToSeptember =
        some (.fired .value) ∧
      pairVerdict? 1 .finish 3 .finish .equal
        juneSecondToSeptemberTwentyNinth = some .notFired := by
  native_decide

/- February reaches day 29 with no year to decide leapness, so a February month-only finish
equals a February 29 finish and not a February 28 one. This is the same yearless maximum the
overlap family compares against. -/
example :
    pairVerdict? 1 .finish 3 .finish .equal
        [storedCell 1 "02/02", storedCell 3 "02-01/02-29"] =
      some (.fired .value) ∧
    pairVerdict? 1 .finish 3 .finish .equal
        [storedCell 1 "02/02", storedCell 3 "02-01/02-28"] = some .notFired := by
  native_decide

/- An empty endpoint on either side leaves the comparison unfired in both directions, and the
result still retains both observations for explanation. -/
example :
    pairResult? 1 .start 3 .start .equal [storedCell 1 "06/09"] = some
        (.yearless (.value { month := 6, day := 1 }) .empty .notFired) ∧
      pairVerdict? 1 .start 3 .start .notEqual [storedCell 1 "06/09"] =
        some .notFired ∧
      pairVerdict? 1 .start 3 .start .equal [] = some .notFired := by
  native_decide

end A12Kernel.Conformance.DateRangeBoundComparison
