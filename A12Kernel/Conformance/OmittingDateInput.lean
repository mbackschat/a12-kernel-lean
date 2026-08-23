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

end A12Kernel.Conformance.OmittingDateInput
