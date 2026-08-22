import A12Kernel.Elaboration.DateRangeStoredComparison

/-! # Stored-versus-stored DateRange equality locks

These cases run the complete comparability relation over the eight admitted declaration pairs
and the resolved-identity verdict behind it. Their admission verdicts and runtime rows are the
Kernel rows in the stored-comparison checkpoint, decided and observed on both codegen
strategies at one reviewed revision.
-/

namespace A12Kernel.Conformance.DateRangeStoredComparison

open A12Kernel

private def rangeField (id : FieldId) (name format separator : String)
    (interpretationOfYear : Option DateRangeYearInterpretation := none) :
    FlatFieldDecl := {
  id, name, groupPath := ["Form"]
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator, interpretationOfYear }
}

/-- One field per admitted declaration pair, with a second instance of each profile that has
only one lexical spelling, so every same-component pair is expressible without self-comparison. -/
private def model : FlatModel := {
  fields := [
    rangeField 1 "IsoA" "yyyy-MM-dd" "/",
    rangeField 2 "IsoB" "yyyy-MM-dd" "/",
    rangeField 3 "DottedFull" "dd.MM.yyyy" "-",
    rangeField 4 "YearA" "yyyy" "/",
    rangeField 5 "YearB" "yyyy" "/",
    rangeField 6 "YearMonthA" "yyyy-MM" "/",
    rangeField 7 "YearMonthB" "yyyy-MM" "/",
    rangeField 8 "MonthSlash" "MM" "/",
    rangeField 9 "MonthEmpty" "MM" "",
    rangeField 10 "MonthDaySlash" "MM-dd" "/",
    rangeField 11 "DayMonthDash" "dd.MM" "-",
    rangeField 12 "DayMonthFrom" "dd.MM" "-" (some .anchorStart),
    rangeField 13 "DayMonthTo" "dd.MM" "-" (some .anchorFinish)]
  timeZoneId := "UTC"
  baseYear := some 2020
}

/-- The same declarations with no Base Year, so a yearless class is compared as retained labels
rather than after completion. -/
private def unconfigured : FlatModel := { model with baseYear := none }

private def admittedIn (checkedModel : FlatModel) (left right : FieldId) : Bool :=
  (elaborateDirectDateRangeComparison checkedModel left right .equal).toOption.isSome

private def admitted (left right : FieldId) : Bool := admittedIn model left right

private def refusalIn? (checkedModel : FlatModel) (left right : FieldId)
    (op : EqualityOp := .equal) :
    Option DirectDateRangeComparisonElabError :=
  match elaborateDirectDateRangeComparison checkedModel left right op with
  | .ok _ => none
  | .error error => some error

private def refusal? (left right : FieldId) (op : EqualityOp := .equal) :
    Option DirectDateRangeComparisonElabError :=
  refusalIn? model left right op

/- Every same-component pair is admitted, in either authored order for each of the three
lexical crossings. Spelling therefore never enters the gate: the two full-Date, the two
month-only, and the two day-and-month declarations cross freely. -/
example :
    [admitted 1 2, admitted 1 3, admitted 3 1,
      admitted 4 5, admitted 6 7,
      admitted 8 9, admitted 9 8,
      admitted 10 11, admitted 11 10] =
      [true, true, true, true, true, true, true, true, true] := by
  native_decide

/- Every cross-component pair is refused with the retained profile pair, in either authored
order and identically for `!=`, and the refusal carries the Kernel's compare diagnostic. The
`dd.MM.yyyy` against `dd.MM` row is the separating control: the two share a separator and
differ only in components. -/
example :
    (refusal? 1 4).isSome = true ∧
    (refusal? 1 6).isSome = true ∧
    (refusal? 1 8).isSome = true ∧
    (refusal? 1 10).isSome = true ∧
    (refusal? 4 6).isSome = true ∧
    (refusal? 4 8).isSome = true ∧
    (refusal? 4 10).isSome = true ∧
    (refusal? 6 8).isSome = true ∧
    (refusal? 6 10).isSome = true ∧
    (refusal? 8 10).isSome = true ∧
    refusal? 3 11 =
      some (.componentMismatch (.exact .dayMonthYearDash) .yearlessDayMonthDotted) ∧
    refusal? 11 3 =
      some (.componentMismatch .yearlessDayMonthDotted (.exact .dayMonthYearDash)) ∧
    refusal? 1 4 .notEqual =
      some (.componentMismatch (.exact .isoSlash) .yearFragment) ∧
    (refusal? 1 4).bind DirectDateRangeComparisonElabError.diagnostic? =
      some .invalidCompareToDateRange := by
  native_decide

/-- Classify one stored token exactly as the checked-document route does, so the fixture cannot
disagree with canonical classification. -/
private def storedCellIn (checkedModel : FlatModel) (field : FieldId)
    (stored : String) : ClassifiedCellInput := {
  address := { field, path := [] }
  stored
  raw :=
    match checkedModel.lookupUniqueId field with
    | .ok declaration =>
        match declaration.toDateRangeDeclarationPolicy? with
        | some policy =>
            (classifyStoredDateRangeForModel checkedModel.timeZoneId
              checkedModel.baseYear policy stored).toOption.getD .empty
        | none => .empty
    | .error _ => .empty
}

private def storedCell (field : FieldId) (stored : String) : ClassifiedCellInput :=
  storedCellIn model field stored

private def verdictIn? (checkedModel : FlatModel) (left right : FieldId)
    (op : EqualityOp) (cells : List ClassifiedCellInput) : Option Verdict := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler checkedModel).toOption
  let checked ←
    (elaborateDirectDateRangeComparison checkedModel left right op).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  }).toOption
  let result ← (checked.evaluate .validation document).toOption
  pure result.verdict

private def verdict? (left right : FieldId) (op : EqualityOp)
    (cells : List ClassifiedCellInput) : Option Verdict :=
  verdictIn? model left right op cells

/- Each lexical crossing compares retained identity rather than stored text: an ISO range and
the dotted spelling of the same two days are equal, and so are both month-only and both
day-and-month spellings of the same labels. A stored-text comparison would refuse all three. -/
example :
    verdict? 1 3 .equal
        [storedCell 1 "2020-11-01/2021-02-28",
          storedCell 3 "01.11.2020-28.02.2021"] = some (.fired .value) ∧
    verdict? 8 9 .equal
        [storedCell 8 "06/09", storedCell 9 "0609"] = some (.fired .value) ∧
    verdict? 10 11 .equal
        [storedCell 10 "06-01/09-30",
          storedCell 11 "01.06-30.09"] = some (.fired .value) := by
  native_decide

/- The relation discriminates: one differing endpoint leaves equality unfired on each crossing
and fires inequality on the full-Date one. -/
example :
    verdict? 1 3 .equal
        [storedCell 1 "2020-11-01/2021-02-28",
          storedCell 3 "02.11.2020-28.02.2021"] = some .notFired ∧
    verdict? 1 3 .notEqual
        [storedCell 1 "2020-11-01/2021-02-28",
          storedCell 3 "02.11.2020-28.02.2021"] = some (.fired .value) ∧
    verdict? 8 9 .equal
        [storedCell 8 "06/09", storedCell 9 "0610"] = some .notFired ∧
    verdict? 10 11 .equal
        [storedCell 10 "06-01/09-30",
          storedCell 11 "02.06-30.09"] = some .notFired := by
  native_decide

/- An empty operand on either side leaves both directions unfired, so absence is neither equal
nor unequal, and an all-empty pair behaves the same way. -/
example :
    verdict? 1 3 .equal [storedCell 1 "2020-11-01/2021-02-28"] = some .notFired ∧
    verdict? 1 3 .notEqual [storedCell 1 "2020-11-01/2021-02-28"] =
      some .notFired ∧
    verdict? 1 3 .equal [] = some .notFired ∧
    verdict? 1 3 .notEqual [] = some .notFired := by
  native_decide

/- A declared year interpretation does not enter the comparability gate: it is not part of the
component set, so two `dd.MM` declarations reading their wrap differently still compare. What it
changes is the value each side resolves to, and the comparison sees that. Identical wrapping
stored text under `FROM` and under `TO` is therefore **unequal**, while identical ordered text is
equal, which separates resolved-identity comparison from stored-text comparison on one pair of
declarations. Both overlap operators refuse these same declarations; equality does not. -/
example :
    admitted 12 13 = true ∧
    verdict? 12 13 .equal
        [storedCell 12 "01.11-28.02", storedCell 13 "01.11-28.02"] =
      some .notFired ∧
    verdict? 12 13 .notEqual
        [storedCell 12 "01.11-28.02", storedCell 13 "01.11-28.02"] =
      some (.fired .value) ∧
    verdict? 12 13 .equal
        [storedCell 12 "01.03-31.10", storedCell 13 "01.03-31.10"] =
      some (.fired .value) ∧
    verdict? 12 13 .equal
        [storedCell 12 "01.11-28.02", storedCell 13 "01.03-31.10"] =
      some .notFired := by
  native_decide

/- Removing the Base Year changes neither the gate nor the crossings. The same five component
classes decide admission, and each class still compares its own retained identity: a yearless
class now compares month or month-day labels rather than completed instants, and February 29
remains a real label with no year to make it leap-dependent. -/
example :
    admittedIn unconfigured 8 9 = true ∧
    admittedIn unconfigured 10 11 = true ∧
    (refusalIn? unconfigured 8 10).bind
        DirectDateRangeComparisonElabError.diagnostic? =
      some .invalidCompareToDateRange ∧
    verdictIn? unconfigured 8 9 .equal
        [storedCellIn unconfigured 8 "06/09",
          storedCellIn unconfigured 9 "0609"] = some (.fired .value) ∧
    verdictIn? unconfigured 10 11 .equal
        [storedCellIn unconfigured 10 "06-01/09-30",
          storedCellIn unconfigured 11 "01.06-30.09"] = some (.fired .value) ∧
    verdictIn? unconfigured 10 11 .equal
        [storedCellIn unconfigured 10 "02-01/02-29",
          storedCellIn unconfigured 11 "01.02-29.02"] = some (.fired .value) ∧
    verdictIn? unconfigured 8 9 .notEqual
        [storedCellIn unconfigured 8 "06/09",
          storedCellIn unconfigured 9 "0610"] = some (.fired .value) ∧
    verdictIn? unconfigured 8 9 .equal
        [storedCellIn unconfigured 8 "06/09"] = some .notFired := by
  native_decide

end A12Kernel.Conformance.DateRangeStoredComparison
