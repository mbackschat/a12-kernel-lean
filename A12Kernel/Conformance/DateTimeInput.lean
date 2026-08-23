import A12Kernel.Elaboration.DateTimeInput

/-! # DateTime stored-input conformance locks

Every admission and cause is read off the kernel's own `validateFull` on both codegen strategies at the
[Time/DateTime input checkpoint](../../docs/SOURCES.md). The final example is the exception and says so:
it compares the retained **instant** under two model zones, which validation output does not expose, so
it locks this project's zone account rather than a correspondence. -/

namespace A12Kernel.Conformance.DateTimeInput

open A12Kernel

private def declaration (format : String := "yyyy-MM-dd'T'HH:mm:ss")
    (kind : TemporalKind := .dateTime) : FlatFieldDecl := {
  id := 0
  groupPath := ["Order"]
  name := "At"
  policy := { kind := .temporal kind TemporalComponents.now }
  temporalTargetPolicy := some { format, partialMode := .full }
}

/-- A decidable view of the classified cell: which gate spoke, and for an admitted label the decoded
components rather than the resolved instant, since the instant depends on the zone. -/
private inductive Outcome where
  | presentEmpty
  | rejected (cause : BaseFormalCause)
  | admitted (year : Int) (month day hour minute second : Nat)
  | contextError
  deriving Repr, DecidableEq

private def classify? (text : String) (zoneId : String := "UTC") :
    Option Outcome := do
  let checked ← (certifyDateTimeInputField (declaration)).toOption
  pure <|
    match checked.classifyStoredForModel zoneId text with
    | .error _ => .contextError
    | .ok .presentEmpty => .presentEmpty
    | .ok .empty => .presentEmpty
    | .ok (.rejected cause) => .rejected cause
    | .ok (.parsed (.temporal (.dateTime _ date clock _))) =>
        .admitted date.year date.month date.day
          clock.hour clock.minute clock.second
    | .ok (.parsed _) => .contextError

/- An admitted label decodes both halves, and the seconds are not dropped. -/
example :
    classify? "2024-06-15T14:30:00" = some (.admitted 2024 6 15 14 30 0) ∧
      classify? "2024-06-15T00:00:00" = some (.admitted 2024 6 15 0 0 0) ∧
      classify? "2024-06-15T23:59:59" = some (.admitted 2024 6 15 23 59 59) := by
  native_decide

/- **Spelling and range are one cause.** A width violation in either half, an out-of-range clock
component, and hour 24 all report the format finding — hour 24 is not an end-of-day spelling here any
more than it is on a plain Time field. -/
example :
    classify? "2024-6-15T14:30:00" = some (.rejected .dateFormat) ∧
      classify? "2024-06-15T25:00:00" = some (.rejected .dateFormat) ∧
      classify? "2024-06-15T12:60:00" = some (.rejected .dateFormat) ∧
      classify? "2024-06-15T12:30:60" = some (.rejected .dateFormat) ∧
      classify? "2024-06-15T24:00:00" = some (.rejected .dateFormat) := by
  native_decide

/- The `'T'` is part of the format: a space in that position is refused rather than tolerated, and so is
a label with no separator at all. -/
example :
    classify? "2024-06-15 14:30:00" = some (.rejected .dateFormat) ∧
      classify? "2024-06-1514:30:00" = some (.rejected .dateFormat) := by
  native_decide

/- **Position in time is the other cause, and the floor is the Date's own.** `1583-10-15` is refused
where `1583-10-16` is admitted — the identical boundary, reached with a perfectly well-formed clock, so
the two causes are separated by the date's position alone. -/
example :
    classify? "1583-10-15T00:00:00" = some (.rejected .dateInvalid) ∧
      classify? "1583-10-16T00:00:00" = some (.admitted 1583 10 16 0 0 0) ∧
      classify? "1500-01-01T00:00:00" = some (.rejected .dateInvalid) := by
  native_decide

/- An unreal calendar date is a spelling question rather than a position one, which is the cell that
keeps the two causes from reading as "malformed versus out of range". -/
example :
    classify? "2024-02-30T00:00:00" = some (.rejected .dateFormat) ∧
      classify? "2024-02-29T00:00:00" = some (.admitted 2024 2 29 0 0 0) := by
  native_decide

/- Empty stored text is present and value-free rather than invalid. -/
example :
    classify? "" = some .presentEmpty := by
  native_decide

/- Certification is refused for a declaration this classifier does not own. Both refusals are
**reachable**: the format gate is kind-independent, so a DateTime field may legally declare the clock
format, and the day-first DateTime spelling is not a declarable format at all. -/
example :
    (certifyDateTimeInputField (declaration (format := "HH:mm:ss"))).toOption =
        none ∧
      (certifyDateTimeInputField
        (declaration (format := "dd.MM.yyyy'T'HH:mm:ss"))).toOption = none ∧
      (certifyDateTimeInputField (declaration (kind := .date))).toOption = none ∧
      (certifyDateTimeInputField (declaration)).toOption.isSome = true := by
  native_decide

/- **Internal, not measured.** The same wall label resolves to different instants under two model zones,
which is what makes the retained instant a zone-dependent fact rather than a property of the text.
Validation output carries no instant, so this pins the zone account a later consumer reads. -/
example :
    (do
      let checked ← (certifyDateTimeInputField (declaration)).toOption
      let utc ← (checked.classifyStoredForModel "UTC"
        "2024-06-15T12:00:00").toOption
      let berlin ← (checked.classifyStoredForModel "Europe/Berlin"
        "2024-06-15T12:00:00").toOption
      match utc, berlin with
      | .parsed (.temporal (.dateTime utcInstant _ _ _)),
        .parsed (.temporal (.dateTime berlinInstant _ _ _)) =>
          pure (utcInstant.epochMillis - berlinInstant.epochMillis)
      | _, _ => none) = some 7200000 := by
  native_decide

end A12Kernel.Conformance.DateTimeInput
