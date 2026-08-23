import A12Kernel.Elaboration.NumericComputation.Evaluation
import A12Kernel.Elaboration.NumericValidation.Evaluation

/-! # DateRange-endpoint numeric component locks

`MonthFromDate(StartOfDateRange(X))` is one authored numeric operand: the endpoint alone is not a
number, so the selection and the component travel together into the numeric operand surface.

Two independent gates decide admission, and these cases keep them separated. The **locus** gate is
the ordinary repeatable-operand rule — a row endpoint needs a rule that iterates the row, and no
wildcard form of this operand exists — while the **component** gate is the declared profile's own
component set supplemented by the model's Base Year. The second is deliberately *not* the
exact-value gate a comparable endpoint carries: an unconfigured yearless month range exposes month
and quarter here while a comparison against a full Date refuses it outright.

The runtime cases pin the other half of that decision: a yearless carrier must reach its retained
label rather than fail as a non-exact profile, and neither endpoint may be substituted for the
other.
-/

namespace A12Kernel.Conformance.DateRangeBoundComponent

open A12Kernel

private def rangeField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel) (format : String) (separator : String) :
    FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .dateRange }
  dateRangePolicy := some { format, separator }
}

private def rowExact := rangeField 1 ["Form", "Rows"] "RowDates" [10] "dd.MM.yyyy" "-"
private def rowMonths := rangeField 2 ["Form", "Rows"] "RowMonths" [10] "MM" "/"
private def rowYears := rangeField 3 ["Form", "Rows"] "RowYears" [10] "yyyy" "/"
private def rowMonthDays :=
  rangeField 4 ["Form", "Rows"] "RowMonthDays" [10] "MM-dd" "/"
private def rowYearMonths :=
  rangeField 5 ["Form", "Rows"] "RowYearMonths" [10] "yyyy-MM" "/"
private def rowDayMonths :=
  rangeField 8 ["Form", "Rows"] "RowDayMonths" [10] "dd.MM" "-"
private def scalarExact := rangeField 6 ["Form"] "ScalarDates" [] "dd.MM.yyyy" "-"

private def numberField (id : FieldId) (groupPath : GroupPath) (name : String)
    (scope : List RepeatableLevel) : FlatFieldDecl := {
  id, groupPath, name, repeatableScope := scope
  policy := { kind := .number { scale := 0, signed := false } }
}

private def rootNumber := numberField 7 ["Form"] "RootNum" []

private def fields : List FlatFieldDecl :=
  [rowExact, rowMonths, rowYears, rowMonthDays, rowYearMonths, rowDayMonths,
    scalarExact, rootNumber]

private def model : FlatModel := {
  fields
  repeatableGroups := [
    { level := 10, path := ["Form", "Rows"], repeatability := some 5 }]
}

/-- The same declarations under a declared Base Year, which supplements only the year component. -/
private def baseYearModel : FlatModel := { model with baseYear := some 2024 }

private def path (declaration : FlatFieldDecl) : SurfaceFieldPath :=
  { base := .absolute, groups := declaration.groupPath, field := declaration.name }

private def component (declaration : FlatFieldDecl) (bound : DateRangeBound)
    (part : DateNumericPart) : AuthoredNumericExpr SurfaceNumericAtom :=
  .atom (.dateRangeBoundPart (path declaration) bound part)

private def sixIs (left : AuthoredNumericExpr SurfaceNumericAtom) :
    SurfaceNumericComparison :=
  { op := .ordinary .equal
    left
    right := .literal { value := 6, authoredScale := 0 } }

/-- The iterating locus: the rule's own row binds the operand's level. -/
private def iteratedResult (chosen : FlatModel) (declaration : FlatFieldDecl)
    (bound : DateRangeBound) (part : DateNumericPart) :
    Except NumericValidationElabError (CheckedOrderedNumericComparison chosen) :=
  elaborateRepeatableNumericComparison chosen ["Form", "Rows"]
    (sixIs (component declaration bound part))

/-- A non-iterating locus: the rule group is the root, which binds no row. -/
private def scalarResult (chosen : FlatModel) (declaration : FlatFieldDecl)
    (bound : DateRangeBound) (part : DateNumericPart) :
    Except NumericValidationElabError (CheckedNumericComparison chosen) :=
  elaborateNumericComparison chosen ["Form"]
    (sixIs (component declaration bound part))

private def exposureFailure? (chosen : FlatModel) (declaration : FlatFieldDecl)
    (part : DateNumericPart) : Option KernelStaticDiagnostic :=
  match iteratedResult chosen declaration .start part with
  | .ok _ => none
  | .error cause => cause.dateRangeBoundPartDiagnostic?

/- An exact row endpoint's component is admitted where the rule iterates the row, and refused from
a rule whose locus binds no row. The scalar declaration is admitted at that same non-iterating
locus, so the refusal is the operand's repetition and not the operand shape. -/
example :
    (iteratedResult model rowExact .start .month).isOk = true ∧
      (scalarResult model rowExact .start .month).isOk = false ∧
      (scalarResult model scalarExact .start .month).isOk = true := by
  native_decide

private def scalarFailure? (declaration : FlatFieldDecl)
    (part : DateNumericPart) : Option NumericValidationElabError :=
  match scalarResult model declaration .start part with
  | .ok _ => none
  | .error cause => some cause

/-- The locus class travels on the shared reference resolver, not on this atom's own refusals. -/
private def locusFailure? (declaration : FlatFieldDecl)
    (part : DateNumericPart) : Option KernelStaticDiagnostic :=
  match scalarFailure? declaration part with
  | some (.resolve error) => error.diagnostic?
  | _ => none

/- The refusal at a non-iterating locus is the shared unstarred-repeatable-reference class, reported
before any component check: it fires for a component the profile exposes and for one it withholds
alike, so the exposure gate never masks it. -/
example :
    scalarFailure? rowExact .month =
        some (.resolve (.repeatableReference rowExact.path)) ∧
      locusFailure? rowExact .month = some .noWildcard ∧
      locusFailure? rowMonths .month = some .noWildcard ∧
      locusFailure? rowMonths .year = some .noWildcard := by
  native_decide

/- Neither the locus refusal nor its Kernel class is the exposure one. -/
example :
    (scalarFailure? rowMonths .year).bind
        NumericValidationElabError.dateRangeBoundPartDiagnostic? = none ∧
      KernelStaticDiagnostic.noWildcard.kernelCode = "MVK_NO_WILDCARD" := by
  native_decide

/- The component gate is the declared profile's own component set, with no Base Year to supply a
year. Every row is a measured Kernel verdict; day and year are the two the fragment profiles
withhold. -/
example :
    -- an exact profile exposes all four
    (iteratedResult model rowExact .start .day).isOk = true ∧
      (iteratedResult model rowExact .start .month).isOk = true ∧
      (iteratedResult model rowExact .finish .quarter).isOk = true ∧
      (iteratedResult model rowExact .finish .year).isOk = true ∧
    -- a month-only range exposes month and quarter alone
      exposureFailure? model rowMonths .day = some .wrongDateFormatForOp ∧
      (iteratedResult model rowMonths .start .month).isOk = true ∧
      (iteratedResult model rowMonths .start .quarter).isOk = true ∧
      exposureFailure? model rowMonths .year = some .wrongDateFormatForOp ∧
    -- a year-only range exposes the year alone
      exposureFailure? model rowYears .day = some .wrongDateFormatForOp ∧
      exposureFailure? model rowYears .month = some .wrongDateFormatForOp ∧
      exposureFailure? model rowYears .quarter = some .wrongDateFormatForOp ∧
      (iteratedResult model rowYears .start .year).isOk = true ∧
    -- year and month, but no day
      exposureFailure? model rowYearMonths .day = some .wrongDateFormatForOp ∧
      (iteratedResult model rowYearMonths .start .month).isOk = true ∧
    -- month and day, but no year, in either authored order
      (iteratedResult model rowMonthDays .start .day).isOk = true ∧
      exposureFailure? model rowMonthDays .year = some .wrongDateFormatForOp ∧
      (iteratedResult model rowDayMonths .start .day).isOk = true ∧
      (iteratedResult model rowDayMonths .start .quarter).isOk = true ∧
      exposureFailure? model rowDayMonths .year = some .wrongDateFormatForOp := by
  native_decide

/- A declared Base Year supplements the year component and nothing else, so the same month-only
declaration gains `YearFromDate` while `DayFromDate` stays refused. -/
example :
    (iteratedResult baseYearModel rowMonths .start .year).isOk = true ∧
      (iteratedResult baseYearModel rowMonths .start .quarter).isOk = true ∧
      exposureFailure? baseYearModel rowMonths .day =
        some .wrongDateFormatForOp ∧
      (iteratedResult baseYearModel rowDayMonths .start .year).isOk = true ∧
      (iteratedResult baseYearModel rowDayMonths .start .day).isOk = true ∧
      (iteratedResult baseYearModel rowMonthDays .start .year).isOk = true ∧
      (iteratedResult baseYearModel rowMonthDays .start .day).isOk = true := by
  native_decide

/- The exposure class is the Kernel's own wrong-format code. -/
example :
    KernelStaticDiagnostic.wrongDateFormatForOp.kernelCode =
      "MVK_WRONG_DATE_FORMAT_FOR_OP" := by
  decide

private def present (value : Value) : CheckedCell :=
  { rawPresent := true, parsed := some value, findings := [] }

private def context (cell : CheckedCell) : FlatContext := { read := fun _ => cell }

private def readComponent (cell : CheckedCell) (bound : DateRangeBound)
    (part : DateNumericPart) : NumericOperand :=
  (context cell).resolveDateRangeBoundNumericOperand { id := rowMonths.id }
    bound part

private def dateValue (epochMillis : Int) (year month day : Nat) : DateValue := {
  instant := { epochMillis }
  parts := { year, month, day }
  basis := .storedGregorian
}

private def june2024 : DateValue := dateValue 1717200000000 2024 6 1
private def september2020 : DateValue := dateValue 1601424000000 2020 9 30

private def exactRange : DateRangeValue :=
  { start := june2024, finish := september2020 }

/- An unconfigured yearless carrier reaches its retained label at either end. Selecting through the
exact-value gate instead would report the whole read malformed, which is the defect this pins. -/
example :
    readComponent (present (.dateRange (.yearlessMonth 3 7))) .start .month =
        .value 3 .fixed ∧
      readComponent (present (.dateRange (.yearlessMonth 3 7))) .finish .month =
        .value 7 .fixed ∧
      readComponent (present (.dateRange (.yearlessMonth 3 7))) .finish .quarter =
        .value 3 .fixed := by
  native_decide

/- An exact carrier reads the selected end, not the other one, and exposes the complete component. -/
example :
    readComponent (present (.dateRange (.exact exactRange))) .start .year =
        .value 2024 .fixed ∧
      readComponent (present (.dateRange (.exact exactRange))) .finish .year =
        .value 2020 .fixed ∧
      readComponent (present (.dateRange (.exact exactRange))) .finish .day =
        .value 30 .fixed := by
  native_decide

/- Absence substitutes the same symmetric fillable zero every direct component read does, while
formal unavailability keeps its exact cause and a non-DateRange payload stays malformed. -/
example :
    readComponent (present (.num 1)) .start .month = .unknown .malformed ∧
      readComponent { rawPresent := false, parsed := none, findings := [] }
        .start .month = .value 0 .both ∧
      readComponent
        { rawPresent := true, parsed := none, findings := [.dateRangeFormat] }
        .start .month = .unknown .dateRangeFormat := by
  native_decide

/- The computation surface admits the same operand at its own nonrepeatable boundary, and keeps the
component gate: a Kernel-legal `MonthFromDate(StartOfDateRange(ScalarDates))` computes, while a row
declaration is still refused for crossing a repeatable level. -/
example :
    (elaborateNumericComputationOperation model ["Form"] rootNumber.id
        (component scalarExact .start .month)).isOk = true ∧
      (elaborateNumericComputationOperation model ["Form"] rootNumber.id
        (component rowExact .start .month)).isOk = false := by
  native_decide

end A12Kernel.Conformance.DateRangeBoundComponent
