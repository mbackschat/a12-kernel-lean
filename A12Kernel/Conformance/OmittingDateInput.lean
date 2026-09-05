import A12Kernel.Elaboration.OmittingDateInput

/-! # Component-omitting Date declaration locks

A DATE declaration may carry a format that omits components, so its stored text is shorter than a
complete date and its value denotes an interval or a yearless calendar position. All seven declarations are Kernel-measured, and this capsule owns all seven through the two existing value shapes.

Every named admission and refusal below is read off the kernel's own `validateFull` on **both** codegen strategies, with the compact additions also agreeing with the interpreter. Every retained failure reports `datumFormatFalsch`; the executable classifier has no second rejection arm. Stored texts outside the retained matrix remain externally unverified.

The four **yearless** formats classify into the `MonthDayValue` the DateRange family already uses, because
a month without a year denotes no interval of concrete dates. Their day bound is the month's greatest
possible day with February at 29, locked by the named month-end and compact-order boundaries. -/

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

private def classifyUnder? (baseYear : Option Int) (format text : String) :
    Outcome :=
  match certifyOmittingDateInputField (declaration format) with
  | .error _ => .unowned
  | .ok checked =>
      match checked.classifyStoredForModel baseYear text with
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

/-- The established no-Base-Year reading, which every row below this line keeps. -/
private def classify? (format text : String) : Outcome :=
  classifyUnder? none format text

/- The three canonical spellings are admitted and denote their exact intervals: a year spans January 1
to December 31, and a year-month spans the first to the leap-aware last day of that month. -/
example :
    classify? "yyyy" "2020" = .interval 2020 1 1 2020 12 31 ∧
      classify? "yyyy-MM" "2020-02" = .interval 2020 2 1 2020 2 29 ∧
      classify? "yyyyMM" "202002" = .interval 2020 2 1 2020 2 29 ∧
      classify? "yyyy-MM" "2021-02" = .interval 2021 2 1 2021 2 28 := by
  native_decide

/- The executable classifier has one rejection cause. These retained width, extra-component, and range
failures all report the format finding and none reports the date finding. -/
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

/- All three complete formats belong to the full-Date classifier and remain outside this one. -/
example :
    classify? "yyyy-MM-dd" "2020-06-15" = .unowned ∧
      classify? "dd.MM.yyyy" "15.06.2020" = .unowned ∧
      classify? "yyyyMMdd" "20200615" = .unowned := by
  native_decide

/-! ## Yearless formats -/

/- A yearless month and month-day are admitted and keep their authored components. `MM` carries no day,
so it stores day one, which is what its month check is applied to. -/
example :
    classify? "MM" "06" = .yearless 6 1 ∧
      classify? "MM-dd" "06-15" = .yearless 6 15 ∧
      classify? "MMdd" "0615" = .yearless 6 15 ∧
      classify? "ddMM" "1506" = .yearless 6 15 := by
  native_decide

/- **With no Base Year the day bound is the month's greatest possible day, and February reaches 29.**
No year is available to decide leapness, so the boundary is measured on both sides for a short month and
for February: April 31 is refused where April 30 is admitted, January 31 is admitted, and February 29 is
admitted where February 30 is refused. The Base-Year rows further down are the other half of this rule;
what a naive implementation gets wrong is resolving against a *fixed* year, which neither half does. -/
example :
    classify? "MM-dd" "04-31" = .rejected .dateFormat ∧
      classify? "MM-dd" "04-30" = .yearless 4 30 ∧
      classify? "MM-dd" "01-31" = .yearless 1 31 ∧
      classify? "MM-dd" "02-29" = .yearless 2 29 ∧
      classify? "MM-dd" "02-30" = .rejected .dateFormat ∧
      classify? "MMdd" "0229" = .yearless 2 29 ∧
      classify? "MMdd" "0230" = .rejected .dateFormat ∧
      classify? "ddMM" "2902" = .yearless 2 29 ∧
      classify? "ddMM" "3002" = .rejected .dateFormat ∧
      classify? "ddMM" "3104" = .rejected .dateFormat := by
  native_decide

/- Separator and component order are independent admission axes: removing the dot admits day-month,
while reversing the same compact components into the existing month-day spelling changes the value. -/
example :
    classify? "ddMM" "0611" = .yearless 11 6 ∧
      classify? "dd.MM" "15.06" = .unowned ∧
      classify? "MMdd" "0611" = .yearless 6 11 ∧
      classify? "MMdd" "06-15" = .rejected .dateFormat ∧
      classify? "ddMM" "15-06" = .rejected .dateFormat := by
  native_decide

/- The retained width, range, and separator failures all reach the classifier's sole format cause. -/
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
          match checked.classifyStoredForModel none "02-29" with
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
          match checked.classifyStoredForModel none "2020" with
          | .admitted (.yearBearing (.omittedMonth date)) =>
              some (date.resolve .firstDay).civil.parts.month
          | _ => none) = some 1 := by
  native_decide

/-! ## A declared Base Year tightens the day bound

The bound above holds because no year is available. Declare one and a year *is* available, so February
follows that year's leap rule: `02-29` is admitted under a leap Base Year and refused under a common
one, on bytes that differ in nothing but the declared year
([checkpoint](../../docs/SOURCES.md#src-yearless-day-bound-reads-the-base-year)). February is the only
month whose two answers differ, which is why one witness settles the rule rather than one month of it.

This is a **refinement in the direction the no-Base-Year clause's own reason points**, not an exception
to it: the earlier reading was measured on a model that declared no Base Year and then stated
unconditionally, so the configuration that separates the two accounts was never varied. -/

/- The discriminating pair: one value, two Base Years, opposite verdicts. -/
example :
    classifyUnder? (some 2024) "MM-dd" "02-29" = .yearless 2 29 ∧
      classifyUnder? (some 2023) "MM-dd" "02-29" = .rejected .dateFormat := by
  native_decide

/- The controls that keep it about February's leapness rather than about declaring a Base Year at all:
   February 28 crosses under both years, and a month whose length no year varies is unaffected. -/
example :
    classifyUnder? (some 2023) "MM-dd" "02-28" = .yearless 2 28 ∧
      classifyUnder? (some 2024) "MM-dd" "02-28" = .yearless 2 28 ∧
      classifyUnder? (some 2023) "MM-dd" "04-30" = .yearless 4 30 ∧
      classifyUnder? (some 2024) "MM-dd" "04-30" = .yearless 4 30 ∧
      classifyUnder? (some 2023) "MM-dd" "04-31" = .rejected .dateFormat ∧
      classifyUnder? (some 2024) "MM-dd" "04-31" = .rejected .dateFormat := by
  native_decide

/- The other three yearless spellings take the same tightening, so it belongs to the day bound rather
   than to one format's parser. `MM` supplies day one, which no leap rule can reach — that row is the
   control showing the bound is applied to the *authored* day. -/
example :
    classifyUnder? (some 2023) "MMdd" "0229" = .rejected .dateFormat ∧
      classifyUnder? (some 2024) "MMdd" "0229" = .yearless 2 29 ∧
      classifyUnder? (some 2023) "ddMM" "2902" = .rejected .dateFormat ∧
      classifyUnder? (some 2024) "ddMM" "2902" = .yearless 2 29 ∧
      classifyUnder? (some 2023) "MM" "02" = .yearless 2 1 := by
  native_decide

/- A **century** non-leap year, so the rule is the Gregorian one and not "divisible by four": 1900 is
   not a leap year and 2000 is. Without this pair the implementation could be testing `year % 4`. -/
example :
    classifyUnder? (some 1900) "MM-dd" "02-29" = .rejected .dateFormat ∧
      classifyUnder? (some 2000) "MM-dd" "02-29" = .yearless 2 29 := by
  native_decide

/-! ## Comparison admission

The component set is **derived** from the declared format, and feeding it to the existing direct-comparison
gate reproduces the measured admission matrix. Every row below was read off `rule add --dry-run` at
kernel 30.8.1 over one model declaring the previously known five formats plus a complete one. The two compact yearless spellings share the same derived component sets, so the same gate applies without another comparison rule.

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

/-- Every yearless-real month/day pair in a leap year, so February 29 is included. Exhaustive rather
than sampled: the round-trip below guards an assumption about component order, and a sampled check
leaves the unsampled pairs exactly where an order mistake hides. -/
private def everyMonthDay : List (Nat × Nat) :=
  (List.range 12).flatMap fun monthIndex =>
    let month := monthIndex + 1
    (List.range (YearlessInterval.yearlessLastDay month)).map fun dayIndex =>
      (month, dayIndex + 1)

private def roundTrips (format : OmittingDateFormat) (month day : Nat) : Bool :=
  match CivilDate.ofParts? { year := 2024, month, day } with
  | none => false
  | some date =>
      OmittingDateFormat.parseYearlessComponents? format none
          (OmittingDateFormat.renderCivilText format date) ==
        some { month, day := if format == .month then 1 else day }

/- **A yearless target's store reads back as the components it wrote**, on every real month/day pair
   of a leap year and all four yearless spellings. Each spelling's store is separately measured
   ([checkpoint](../../docs/SOURCES.md#src-base-year-yearless-store)), so this case is not what
   establishes the component order; it is what keeps the two directions from drifting apart later,
   since a change to either one alone breaks it on every pair whose month and day differ. `MM` writes
   no day and reads back the implied day one. -/
example : [OmittingDateFormat.month, .monthDay, .monthDayConcatenated,
    .dayMonthConcatenated].map (fun format =>
      everyMonthDay.all fun pair => roundTrips format pair.1 pair.2) =
    [true, true, true, true] := by
  native_decide

/- The exhaustive pass above would also hold for a renderer that confused the two compact spellings
   if their parsers agreed, so this is the separator: one date whose month and day differ renders to
   two different texts under the two compact formats, and each is refused by the other's reading. -/
example : ((CivilDate.ofParts? { year := 2024, month := 6, day := 11 }).map fun date =>
      (OmittingDateFormat.renderCivilText .monthDayConcatenated date,
        OmittingDateFormat.renderCivilText .dayMonthConcatenated date)) =
    some ("0611", "1106") := by
  native_decide

end A12Kernel.Conformance.OmittingDateInput
