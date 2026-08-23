import A12Kernel.Elaboration.PartialDateInput

/-! # Partially known Date stored-input conformance locks

Every **admission and cause** below is read off the kernel's own `validateFull` on both codegen
strategies at the partial-precision checkpoint in [`SOURCES.md`](../../docs/SOURCES.md), not from this
implementation. The rows are chosen so each one moves exactly one thing: the omission depth, the
declared precision, the spelling, the calendar reality of a present component, or the position in time.

The last two examples are different and are marked where they sit: they pin the admitted **value's own
identity** and its leap-aware boundaries, which no validation output exposes — a partial value reaches
an observable form only once `ValueAsDate` selects an endpoint. They are internal representation locks,
not correspondence claims. -/

namespace A12Kernel.Conformance.PartialDateInput

open A12Kernel

private def declaration (mode : TemporalPartialMode)
    (before1900 : Bool := false) (format : String := "yyyy-MM-dd") : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "P"
  policy := { kind := .temporal .date TemporalComponents.fullDate }
  temporalTargetPolicy := some {
    format
    partialMode := mode
    youngerThan1900Check := before1900 }
}

/-- The classified outcome projected to a decidable view: the admitted case's own value is checked
separately, because most rows are about *which* gate spoke rather than about the value. -/
private inductive Outcome where
  | empty
  | rejected (cause : BaseFormalCause)
  | admitted
  deriving Repr, DecidableEq

private def classify? (mode : TemporalPartialMode) (text : String)
    (before1900 : Bool := false) (format : String := "yyyy-MM-dd") :
    Option Outcome := do
  let checked ←
    (certifyPartialDateInputField (declaration mode before1900 format)).toOption
  pure <| match checked.classifyStored text with
    | .presentEmpty => .empty
    | .rejected cause => .rejected cause
    | .admitted _ => .admitted

/- The precision ladder, measured. Each precision admits exactly one more omission depth than the one
before it, and every depth it does *not* admit is refused as an omission failure rather than as a
spelling one. Reading the three columns across is what shows the staircase; reading one row down shows
that the refusal cause never changes with the depth. -/
example :
    classify? .dayOptional "2024-06-15" = some .admitted ∧
      classify? .monthOptional "2024-06-15" = some .admitted ∧
      classify? .yearOptional "2024-06-15" = some .admitted := by
  native_decide

example :
    classify? .dayOptional "2024-06-00" = some .admitted ∧
      classify? .monthOptional "2024-06-00" = some .admitted ∧
      classify? .yearOptional "2024-06-00" = some .admitted := by
  native_decide

example :
    classify? .dayOptional "2024-00-00" = some (.rejected .dateInvalid) ∧
      classify? .monthOptional "2024-00-00" = some .admitted ∧
      classify? .yearOptional "2024-00-00" = some .admitted := by
  native_decide

example :
    classify? .dayOptional "0000-00-00" = some (.rejected .dateInvalid) ∧
      classify? .monthOptional "0000-00-00" = some (.rejected .dateInvalid) ∧
      classify? .yearOptional "0000-00-00" = some .admitted := by
  native_decide

/- A zero pattern that is **not a monotone suffix** is refused at every precision, including the
deepest — which is the row that keeps `yearOptional` from reading as "admits any zeros". A present day
beside an omitted month, a present month and day beside an omitted year, and a present day beside both
omitted are three distinct non-suffix shapes and all three refuse identically. -/
example :
    classify? .yearOptional "2024-00-15" = some (.rejected .dateInvalid) ∧
      classify? .yearOptional "0000-06-15" = some (.rejected .dateInvalid) ∧
      classify? .yearOptional "0000-00-15" = some (.rejected .dateInvalid) ∧
      classify? .dayOptional "2024-00-15" = some (.rejected .dateInvalid) := by
  native_decide

/- **The two causes split on reality, not on legality.** An impossible calendar date is the *format*
cause even though its spelling is well formed and its declaration could hold a value there — and so is
an impossible month standing beside a legally omitted day, which is the sharpest cell of the whole
matrix: the omission is admitted, the month is not, and the month's cause wins. A width violation is
the same cause, which is what keeps that cause from reading as "spelling only". -/
example :
    classify? .yearOptional "2024-02-30" = some (.rejected .dateFormat) ∧
      classify? .dayOptional "2024-13-00" = some (.rejected .dateFormat) ∧
      classify? .yearOptional "2024-6-15" = some (.rejected .dateFormat) ∧
      classify? .dayOptional "2024-12-00" = some .admitted := by
  native_decide

/- **Position in time is the other cause, and it is decided after reality.** An omitted-day value whose
earliest completion is real but below the universal Gregorian floor is the *date* cause, not the format
cause — the distinction the implementation originally got wrong, because the floor test lives inside
the value constructor and a `none` from it would otherwise read as unreality. The adjacent admitted row
one month later pins that the floor rather than the year is doing the work. -/
example :
    classify? .dayOptional "1583-10-00" = some (.rejected .dateInvalid) ∧
      classify? .dayOptional "1583-11-00" = some .admitted ∧
      classify? .dayOptional "1583-11-00" (before1900 := true) =
        some (.rejected .dateInvalid) := by
  native_decide

/- The optional pre-1900 check moves the same boundary without changing the cause, so a consumer cannot
tell the two thresholds apart from the cause alone — only from the declaration. -/
example :
    classify? .dayOptional "1899-12-00" (before1900 := true) =
        some (.rejected .dateInvalid) ∧
      classify? .dayOptional "1899-12-00" = some .admitted ∧
      classify? .dayOptional "1900-01-00" (before1900 := true) = some .admitted := by
  native_decide

/- Empty text is present-empty at every precision: emptiness is not invalidity, and no component is
read before that is decided. -/
example :
    classify? .dayOptional "" = some .empty ∧
      classify? .yearOptional "" = some .empty := by
  native_decide

/- A **full-precision** declaration is refused certification rather than classified, so the two input
classifiers never both claim one declaration. Measured, such a declaration reports every omission
marker as the format cause, which is [`FullDateInput.lean`](../Elaboration/FullDateInput.lean)'s to
report and deliberately not this classifier's. -/
example :
    classify? .full "2024-06-00" = none ∧
      classify? .full "2024-06-15" = none := by
  native_decide

/- The whole rule is **independent of the declared spelling**. The German `dd.MM.yyyy` declaration
reproduces the ladder, the non-suffix refusal, the reality-before-position order, and the floor cause
cell for cell, so the omission marker is the zero *component* rather than a position in the ISO text.
Measured on the same model as the rows above. -/
example :
    classify? .dayOptional "00.06.2024" (format := "dd.MM.yyyy") = some .admitted ∧
      classify? .dayOptional "00.00.2024" (format := "dd.MM.yyyy") =
        some (.rejected .dateInvalid) ∧
      classify? .monthOptional "00.00.2024" (format := "dd.MM.yyyy") =
        some .admitted ∧
      classify? .yearOptional "15.00.2024" (format := "dd.MM.yyyy") =
        some (.rejected .dateInvalid) ∧
      classify? .dayOptional "00.13.2024" (format := "dd.MM.yyyy") =
        some (.rejected .dateFormat) ∧
      classify? .dayOptional "00.10.1583" (format := "dd.MM.yyyy") =
        some (.rejected .dateInvalid) := by
  native_decide

/- **Internal, not measured.** The admitted value is the one the shape denotes, not merely "some
value": an omitted day carries the month's two boundaries, and an omitted month carries the year's.
Validation output cannot see this, so these two examples lock the representation a later `ValueAsDate`
consumer reads rather than a kernel correspondence. -/
private def admittedValue? (mode : TemporalPartialMode) (text : String) :
    Option PartiallyKnownDateValue := do
  let checked ← (certifyPartialDateInputField (declaration mode)).toOption
  match checked.classifyStored text with
  | .admitted value => some value.value
  | _ => none

example :
    admittedValue? .dayOptional "2024-02-00" =
        (OmittedDayDate.ofYearMonth? 2024 2).map .omittedDay ∧
      admittedValue? .monthOptional "2024-00-00" =
        (OmittedMonthDate.ofYear? 2024).map .omittedMonth ∧
      admittedValue? .yearOptional "0000-00-00" = some .omittedYear := by
  native_decide

/- Leap awareness reaches the omitted day's *latest* boundary, which is the half a consumer selecting
`LastDay` reads. February 2024 ends on the 29th and February 2023 on the 28th, from stored text that
differs only in its year. -/
example :
    (admittedValue? .dayOptional "2024-02-00").isSome = true ∧
      ((OmittedDayDate.ofYearMonth? 2024 2).map
        (·.resolve .lastDay)).isSome = true ∧
      (OmittedDayDate.ofYearMonth? 2024 2).map (·.resolve .lastDay) ≠
        (OmittedDayDate.ofYearMonth? 2023 2).map (·.resolve .lastDay) := by
  native_decide

/- **What a partial value says, against what it denotes.** Measured on the kernel's own `validateFull`,
a rule message interpolating one of these values prints its **zero markers literally**: stored
`2024-06-00` renders `06/00/2024`, `2024-00-00` renders `00/00/2024`, and `0000-00-00` renders
`00/00/0000`. So the stored components are the renderer's input and a completion is not — the earliest
boundary of that first value is June **1st**, which is what a consumer reaching for `resolve` would
print instead. These rows pin the projection that keeps those two apart. The rendered
*pattern* follows the **message locale** — one unchanged declaration renders `06/15/2024` under en_US
and `15.06.2024` under de_DE — so it is presentation and stays outside this projection, while the
components below are the semantics and travel with their marker. -/
example :
    (admittedValue? .dayOptional "2024-06-00").map (·.storedComponents) =
        some (some 2024, some 6, none) ∧
      (admittedValue? .monthOptional "2024-00-00").map (·.storedComponents) =
        some (some 2024, none, none) ∧
      (admittedValue? .yearOptional "0000-00-00").map (·.storedComponents) =
        some (none, none, none) ∧
      (admittedValue? .dayOptional "2024-06-15").map (·.storedComponents) =
        some (some 2024, some 6, some 15) := by
  native_decide

/- The nearest wrong reading, made explicit: the omitted day's own earliest boundary carries day `1`,
so a renderer built on `resolve` prints a day the stored value never spelled. -/
example :
    (OmittedDayDate.ofYearMonth? 2024 6).map
        (fun boundary => (boundary.resolve .firstDay).civil.parts.day) =
        some 1 ∧
      (admittedValue? .dayOptional "2024-06-00").map
        (fun value => value.storedComponents.2.2) = some none := by
  native_decide

end A12Kernel.Conformance.PartialDateInput
