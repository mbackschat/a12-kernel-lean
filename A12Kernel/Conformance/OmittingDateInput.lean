import A12Kernel.Elaboration.OmittingDateInput

/-! # Component-omitting Date declaration locks

A DATE declaration may carry a format that omits components, so its stored text is shorter than a
complete date and its value denotes an interval. All five such formats are legal declarations, measured
`KERNEL_CONFIRMED`; this capsule owns the three whose value shape already exists here.

Every admission and refusal below is read off the kernel's own `validateFull` on **both** codegen
strategies, which agreed on all eleven observed rows. The result is uniform: **one cause**,
`datumFormatFalsch`, for every spelling failure, with no position-in-time cause anywhere, because these
formats carry no complete date to fall below a floor.

`MM` and `MM-dd` are deliberately outside this capsule. Both are measured legal and their canonical text
is measured accepted — `06` and `06-15`, with `02-29` accepted and `02-30` refused, so a yearless
month-day is leap-capable. Representing them needs a yearless value shape this project holds only inside
the DateRange family, and joining those domains is its own unit rather than a widening here. -/

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
      | .admitted value =>
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

/- Certification is refused for a declaration this classifier does not own: the two **complete** formats
belong to the full-Date classifier, and the two yearless formats have no value shape here yet. Both
refusals are reachable, since all four are legal declarations. -/
example :
    classify? "yyyy-MM-dd" "2020-06-15" = .unowned ∧
      classify? "dd.MM.yyyy" "15.06.2020" = .unowned ∧
      classify? "MM" "06" = .unowned ∧
      classify? "MM-dd" "06-15" = .unowned := by
  native_decide

/- The admitted value is a **partially known Date** in the existing domain, not a new one, so every
`ValueAsDate` consumer reads it through the endpoint resolver it already has. -/
example :
    (match certifyOmittingDateInputField (declaration "yyyy") with
      | .error _ => none
      | .ok checked =>
          match checked.classifyStored "2020" with
          | .admitted (.omittedMonth date) =>
              some (date.resolve .firstDay).civil.parts.month
          | _ => none) = some 1 := by
  native_decide

end A12Kernel.Conformance.OmittingDateInput
