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

private def admitted (left right : FieldId) : Bool :=
  (elaborateDirectDateRangeComparison model left right .equal).toOption.isSome

private def refusal? (left right : FieldId) (op : EqualityOp := .equal) :
    Option DirectDateRangeComparisonElabError :=
  match elaborateDirectDateRangeComparison model left right op with
  | .ok _ => none
  | .error error => some error

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

private def verdict? (left right : FieldId) (op : EqualityOp)
    (cells : List ClassifiedCellInput) : Option Verdict := do
  let prepared ← (prepareFlatStringContext { now := { epochMillis := 0 } }
    builtinStringPatternCompiler model).toOption
  let checked ← (elaborateDirectDateRangeComparison model left right op).toOption
  let document ← (checkDocument prepared "en_US" {
    instantiatedRows := []
    cells
  }).toOption
  let result ← (checked.evaluate .validation document).toOption
  pure result.verdict

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

end A12Kernel.Conformance.DateRangeStoredComparison
