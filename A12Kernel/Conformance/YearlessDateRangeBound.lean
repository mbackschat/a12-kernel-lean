import A12Kernel.Elaboration.YearlessDateRangeBound

/-! # Unconfigured yearless DateRange bound locks

These cases run the whole route for a model with no Base Year: which numeric components each
yearless declaration exposes, which the Kernel refuses, and the retained labels each endpoint
selects. The admission verdicts and the filled component values are the Kernel rows in the
unconfigured-bound checkpoint, decided and observed on both codegen strategies. The empty and
formally invalid rows are internal compositions of the shared empty and unknown projections;
no observation covers them on this route.
-/

namespace A12Kernel.Conformance.YearlessDateRangeBound

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
    rangeField 4 "DayMonthDash" "dd.MM" "-",
    rangeField 5 "YearA" "yyyy" "/",
    rangeField 6 "YearMonthA" "yyyy-MM" "/",
    rangeField 7 "IsoA" "yyyy-MM-dd" "/"]
  timeZoneId := "UTC"
}

private def configured : FlatModel := { model with baseYear := some 2020 }

private def componentError? (checkedModel : FlatModel) (source : FieldId)
    (bound : DateRangeBound) (part : DateNumericPart) :
    Option YearlessDateRangeBoundElabError :=
  match elaborateYearlessDateRangeBoundComponent checkedModel source bound part with
  | .ok _ => none
  | .error error => some error

private def componentAdmitted (source : FieldId) (bound : DateRangeBound)
    (part : DateNumericPart) : Bool :=
  (componentError? model source bound part).isNone

/- Extraction itself is admitted on every yearless declaration with no Base Year, and each
declaration exposes exactly the components it retains. Month-only exposes month and quarter;
month-and-day additionally exposes the day. Both lexical spellings of each component set behave
alike, so the spelling never enters the gate. -/
example :
    [componentAdmitted 1 .start .month, componentAdmitted 1 .start .quarter,
      componentAdmitted 1 .finish .month,
      componentAdmitted 2 .start .month,
      componentAdmitted 3 .start .day, componentAdmitted 3 .start .month,
      componentAdmitted 3 .finish .day, componentAdmitted 3 .start .quarter,
      componentAdmitted 4 .start .day, componentAdmitted 4 .finish .month] =
      List.replicate 10 true := by
  native_decide

/- A component the declaration does not retain is refused with the Kernel's wrong-format
diagnostic rather than being completed to a zero the caller could read. -/
example :
    componentError? model 1 .start .day =
        some (.componentNotExposed 1 .day) ∧
      componentError? model 1 .start .year =
        some (.componentNotExposed 1 .year) ∧
      componentError? model 3 .start .year =
        some (.componentNotExposed 3 .year) ∧
      (componentError? model 1 .start .day).bind
        YearlessDateRangeBoundElabError.diagnostic? =
      some .wrongDateFormatForOp ∧
    KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode =
      "MVK_WRONG_DATE_FORMAT_FOR_OP" := by
  native_decide

/- The two routing refusals keep this owner narrow: a year-bearing declaration and a configured
model both belong to the exact-valued owner, and neither carries a Kernel diagnostic, because
the Kernel admits both there rather than refusing them. -/
example :
    componentError? model 5 .start .year = some (.notYearless 5 "yyyy" "/") ∧
    componentError? model 6 .start .month =
      some (.notYearless 6 "yyyy-MM" "/") ∧
    componentError? model 7 .start .day =
      some (.notYearless 7 "yyyy-MM-dd" "/") ∧
    componentError? configured 1 .start .month =
      some (.baseYearConfigured 1) ∧
    (componentError? configured 1 .start .month).bind
      YearlessDateRangeBoundElabError.diagnostic? = none := by
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

private def componentResult? (source : FieldId) (bound : DateRangeBound)
    (part : DateNumericPart) (cells : List ClassifiedCellInput) :
    Option YearlessDateRangeBoundComponentResult := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ←
    (elaborateYearlessDateRangeBoundComponent model source bound part).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  }).toOption
  (checked.evaluate document).toOption

/- Each endpoint selects the labels its own position retains, and the numeric component reads
them without a manufactured year: June through September exposes month 6 at the start and 9 at
the finish, and the start's quarter is the second. -/
example :
    componentResult? 1 .start .month [storedCell 1 "06/09"] = some {
      selected := .value (.month 6)
      component := .value 6 .fixed } ∧
    componentResult? 1 .finish .month [storedCell 1 "06/09"] = some {
      selected := .value (.month 9)
      component := .value 9 .fixed } ∧
    componentResult? 1 .start .quarter [storedCell 1 "06/09"] = some {
      selected := .value (.month 6)
      component := .value 2 .fixed } ∧
    componentResult? 2 .start .month [storedCell 2 "0609"] = some {
      selected := .value (.month 6)
      component := .value 6 .fixed } := by
  native_decide

/- A month-and-day declaration retains both labels at each endpoint, under either spelling. -/
example :
    componentResult? 3 .start .day [storedCell 3 "06-01/09-30"] = some {
      selected := .value (.monthDay { month := 6, day := 1 })
      component := .value 1 .fixed } ∧
    componentResult? 3 .finish .day [storedCell 3 "06-01/09-30"] = some {
      selected := .value (.monthDay { month := 9, day := 30 })
      component := .value 30 .fixed } ∧
    componentResult? 3 .finish .month [storedCell 3 "06-01/09-30"] = some {
      selected := .value (.monthDay { month := 9, day := 30 })
      component := .value 9 .fixed } ∧
    componentResult? 4 .start .day [storedCell 4 "01.06-30.09"] = some {
      selected := .value (.monthDay { month := 6, day := 1 })
      component := .value 1 .fixed } := by
  native_decide

/- An empty range keeps the shared empty projection: the endpoint observes empty and the
component substitutes symmetric zero rather than a label. A formally invalid stored value keeps
its exact cause through the same read. -/
example :
    componentResult? 1 .start .month [] = some {
      selected := .empty
      component := .value 0 .both } ∧
    componentResult? 1 .start .month [storedCell 1 "13/09"] = some {
      selected := .unknown .dateRangeFormat
      component := .unknown .dateRangeFormat } := by
  native_decide

end A12Kernel.Conformance.YearlessDateRangeBound
