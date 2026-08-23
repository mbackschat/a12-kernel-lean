import A12Kernel.Elaboration.OmittingDateInput

/-! # Component-omitting Date declaration locks

A DATE declaration may carry a format that omits components, so its stored text is shorter than a
complete date and its value denotes an interval. All five such formats are legal declarations, measured
`KERNEL_CONFIRMED`; this capsule owns the three whose value shape already exists here.

Every admission and refusal below is read off the kernel's own `validateFull` on **both** codegen
strategies, which agreed on all eleven observed rows. The result is uniform: **one cause**,
`datumFormatFalsch`, for every spelling failure, with no position-in-time cause anywhere, because these
formats carry no complete date to fall below a floor.

The two **yearless** formats classify into the `MonthDayValue` the DateRange family already uses, because
a month without a year denotes no interval of concrete dates. Their day bound is the month's greatest
possible day with February at 29, measured across the whole boundary. -/

namespace A12Kernel.Conformance.OmittingDateInput

open A12Kernel

private def declaration (format : String) : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "Period"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some { format, partialMode := .full }
}

/-- A decidable view: which gate spoke, and for an admitted text the interval it denotes. -/
private inductive Outcome where
  | presentEmpty
  | rejected (cause : BaseFormalCause)
  | interval (firstYear : Int) (firstMonth firstDay : Nat)
      (lastYear : Int) (lastMonth lastDay : Nat)
  /-- A yearless position: no year, and therefore no interval of concrete dates. -/
  | yearless (month day : Nat)
  | unowned
  deriving Repr, DecidableEq

private def intervalOf (first last : FullDate) : Outcome :=
  .interval first.civil.parts.year first.civil.parts.month first.civil.parts.day
    last.civil.parts.year last.civil.parts.month last.civil.parts.day

private def classify? (format text : String) : Outcome :=
  match certifyOmittingDateInputField (declaration format) with
  | .error _ => .unowned
  | .ok checked =>
      match checked.classifyStored text with
      | .presentEmpty => .presentEmpty
      | .rejected cause => .rejected cause
      | .admitted (.yearless value) => .yearless value.month value.day
      | .admitted (.yearBearing value) =>
          match value with
          | .omittedMonth date =>
              intervalOf (date.resolve .firstDay) (date.resolve .lastDay)
          | .omittedDay date =>
              intervalOf (date.resolve .firstDay) (date.resolve .lastDay)
          | .full date => intervalOf date date
          | .omittedYear => .unowned

/- The three canonical spellings are admitted and denote their exact intervals: a year spans January 1
to December 31, and a year-month spans the first to the leap-aware last day of that month. -/
example :
    classify? "yyyy" "2020" = .interval 2020 1 1 2020 12 31 ∧
      classify? "yyyy-MM" "2020-02" = .interval 2020 2 1 2020 2 29 ∧
      classify? "yyyyMM" "202002" = .interval 2020 2 1 2020 2 29 ∧
      classify? "yyyy-MM" "2021-02" = .interval 2021 2 1 2021 2 28 := by
  native_decide

/- **Widths are fixed and one cause covers every spelling failure.** A short year, a year carrying extra
components, and an out-of-range month all report the format finding, and none reports the date finding —
these formats carry no complete date whose position could fall below the floor. -/
example :
    classify? "yyyy" "20" = .rejected .dateFormat ∧
      classify? "yyyy" "2020-06" = .rejected .dateFormat ∧
      classify? "yyyy-MM" "2020-13" = .rejected .dateFormat ∧
      classify? "yyyy-MM" "2020-00" = .rejected .dateFormat := by
  native_decide

/- **The separator is exact in both directions**, which is the pair that keeps `yyyy-MM` and `yyyyMM`
from collapsing into one lenient parser: each refuses the other's spelling. -/
example :
    classify? "yyyy-MM" "202006" = .rejected .dateFormat ∧
      classify? "yyyyMM" "2020-06" = .rejected .dateFormat := by
  native_decide

/- Empty stored text is present and value-free rather than invalid, as everywhere else in this family. -/
example :
    classify? "yyyy" "" = .presentEmpty ∧
      classify? "yyyy-MM" "" = .presentEmpty := by
  native_decide

/- Certification is refused only for the two **complete** formats, which belong to the full-Date
classifier. Both refusals are reachable, since both are legal declarations. -/
example :
    classify? "yyyy-MM-dd" "2020-06-15" = .unowned ∧
      classify? "dd.MM.yyyy" "15.06.2020" = .unowned := by
  native_decide

/-! ## Yearless formats -/

/- A yearless month and month-day are admitted and keep their authored components. `MM` carries no day,
so it stores day one, which is what its month check is applied to. -/
example :
    classify? "MM" "06" = .yearless 6 1 ∧
      classify? "MM-dd" "06-15" = .yearless 6 15 := by
  native_decide

/- **The day bound is the month's greatest possible day, and February reaches 29.** No year is available
to decide leapness, so the boundary is measured on both sides for a short month and for February: April
31 is refused where April 30 is admitted, January 31 is admitted, and February 29 is admitted where
February 30 is refused. This is the row a naive implementation gets wrong by resolving against a specific
year. -/
example :
    classify? "MM-dd" "04-31" = .rejected .dateFormat ∧
      classify? "MM-dd" "04-30" = .yearless 4 30 ∧
      classify? "MM-dd" "01-31" = .yearless 1 31 ∧
      classify? "MM-dd" "02-29" = .yearless 2 29 ∧
      classify? "MM-dd" "02-30" = .rejected .dateFormat := by
  native_decide

/- Widths, ranges, and the separator are exact here too, and every failure is the same one cause: a month
carrying an extra component, a zero month, a short month or day, a zero day, a missing separator, and an
out-of-range month all report the format finding. -/
example :
    classify? "MM" "06-15" = .rejected .dateFormat ∧
      classify? "MM" "00" = .rejected .dateFormat ∧
      classify? "MM" "13" = .rejected .dateFormat ∧
      classify? "MM" "6" = .rejected .dateFormat ∧
      classify? "MM-dd" "6-15" = .rejected .dateFormat ∧
      classify? "MM-dd" "06-5" = .rejected .dateFormat ∧
      classify? "MM-dd" "06-00" = .rejected .dateFormat ∧
      classify? "MM-dd" "0615" = .rejected .dateFormat ∧
      classify? "MM-dd" "13-01" = .rejected .dateFormat := by
  native_decide

/- A yearless value has **no** interval form, which is the distinction the two-armed result exists to
keep: nothing here can hand a consumer a `FullDate` it would then compare against a dated operand. -/
example :
    (match certifyOmittingDateInputField (declaration "MM-dd") with
      | .error _ => none
      | .ok checked =>
          match checked.classifyStored "02-29" with
          | .admitted (.yearless _) => some true
          | .admitted (.yearBearing _) => some false
          | _ => none) = some true := by
  native_decide

/- The admitted value is a **partially known Date** in the existing domain, not a new one, so every
`ValueAsDate` consumer reads it through the endpoint resolver it already has. -/
example :
    (match certifyOmittingDateInputField (declaration "yyyy") with
      | .error _ => none
      | .ok checked =>
          match checked.classifyStored "2020" with
          | .admitted (.yearBearing (.omittedMonth date)) =>
              some (date.resolve .firstDay).civil.parts.month
          | _ => none) = some 1 := by
  native_decide

/-! ## Comparison admission

The component set is **derived** from the declared format, and feeding it to the existing direct-comparison
gate reproduces the measured admission matrix. Every row below was read off `rule add --dry-run` at
kernel 30.8.1 over one model declaring all five formats plus a complete one.

No new comparison rule was needed, which is the point of measuring this: the gate is **year presence**
after optional Base-Year supplementation plus date-class agreement, and it already said so. -/

private def admits (left right : String) (hasBaseYear : Bool := false) : Bool :=
  match OmittingDateFormat.ofSource? left, OmittingDateFormat.ofSource? right with
  | some leftFormat, some rightFormat =>
      TemporalComparisonOp.admitsFormats .equal hasBaseYear
        leftFormat.components rightFormat.components
  | _, _ => false

private def admitsComplete (yearless : String) (hasBaseYear : Bool := false) : Bool :=
  match OmittingDateFormat.ofSource? yearless with
  | some format =>
      TemporalComparisonOp.admitsFormats .equal hasBaseYear format.components
        TemporalComponents.fullDate
  | none => false

/- **Component sets need not agree; year presence must.** A year-only operand compares with a year-month
one and with a complete date, which is what makes this gate a year test rather than a format test. -/
example :
    admits "yyyy" "yyyy" = true ∧
      admits "yyyy" "yyyy-MM" = true ∧
      admits "yyyy-MM" "yyyyMM" = true ∧
      admitsComplete "yyyy" = true ∧
      admitsComplete "yyyy-MM" = true := by
  native_decide

/- **A yearless operand is refused against a year-bearing one**, and admitted against another yearless
one. That pair is the measured separator: without it the gate would read as "any two Date formats
compare". -/
example :
    admits "MM-dd" "yyyy" = false ∧
      admits "MM" "yyyy-MM" = false ∧
      admitsComplete "MM-dd" = false ∧
      admits "MM-dd" "MM-dd" = true ∧
      admits "MM" "MM-dd" = true := by
  native_decide

/- A declared **Base Year** supplies the missing year and makes the refused pairs compare, which is why
the gate supplements before testing rather than after. -/
example :
    admits "MM-dd" "yyyy" (hasBaseYear := true) = true ∧
      admitsComplete "MM-dd" (hasBaseYear := true) = true := by
  native_decide

/- The derived component sets are exactly what the stored text carries, so no declaration can expose a
component it has no way to store. -/
example :
    (OmittingDateFormat.year.components.year,
        OmittingDateFormat.year.components.month) = (true, false) ∧
      (OmittingDateFormat.monthDay.components.year,
        OmittingDateFormat.monthDay.components.day) = (false, true) ∧
      OmittingDateFormat.month.components.hasDate = true ∧
      OmittingDateFormat.monthDay.components.hasTime = false := by
  native_decide

end A12Kernel.Conformance.OmittingDateInput
