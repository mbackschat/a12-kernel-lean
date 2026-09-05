import A12Kernel.Semantics.Observation

/-! # Observation conformance locks

Small executable examples for the phase-sensitive cell boundary. These are semantic
fixtures, not a transcription of any engine implementation.
-/

namespace A12Kernel.Conformance.Observation

open A12Kernel

private def optionalNumber : FieldPolicy :=
  { kind := .number { scale := 2, signed := false } }

private def confirm : FieldPolicy :=
  { kind := .confirm }

private def string : FieldPolicy :=
  { kind := .string }

private def fullDateComponents : TemporalComponents :=
  { year := true, month := true, day := true,
    hour := false, minute := false, second := false }

private def date : FieldPolicy :=
  { kind := .temporal .date fullDateComponents }

private def clockComponents : TemporalComponents :=
  { year := false, month := false, day := false,
    hour := true, minute := true, second := true }

/-- A **DATE** declaration whose format is a clock, which the Kernel treats as a time-valued field
throughout — admission, store, and comparison alike. -/
private def dateAtClockFormat : FieldPolicy :=
  { kind := .temporal .date clockComponents }

/-- The mirror: a **TIME** declaration whose format is a calendar date. -/
private def timeAtDateFormat : FieldPolicy :=
  { kind := .temporal .time fullDateComponents }

private def dateRange : FieldPolicy :=
  { kind := .dateRange }

private def dateParts : DateParts :=
  { year := 2024, month := 6, day := 25 }

private def clock : TimeOfDay :=
  (TimeOfDay.ofHms? 5 21 7).get (by native_decide)

private def temporalValue (kind : TemporalKind) (instant : Instant) : Value :=
  match kind with
  | .date => .temporal (.date { instant, parts := dateParts, basis := .storedGregorian })
  | .time => .temporal (.time instant clock)
  | .dateTime =>
      .temporal (.dateTime instant dateParts clock .storedGregorian)

private def dateRangeValue : DateRangeValue :=
  { start := {
      instant := { epochMillis := 100000 }
      parts := { year := 2024, month := 6, day := 25 }
      basis := .storedGregorian }
    finish := {
      instant := { epochMillis := 200000 }
      parts := { year := 2024, month := 6, day := 30 }
      basis := .storedGregorian } }

private def requiredEmpty : CheckedCell :=
  (formalCheck optionalNumber .empty).withFinding .required

example : formalCheck optionalNumber .empty =
    { rawPresent := false, parsed := none, findings := [] } := by
  decide

example : observeCell .validation (formalCheck optionalNumber .empty) = .empty := by
  rfl

example : observeCell .computation (formalCheck optionalNumber .empty) = .empty := by
  rfl

example : formalCheck string .presentEmpty =
    { rawPresent := true, parsed := none, findings := [] } := by
  decide

example : formalCheck string (.parsed (.str "")) = formalCheck string .presentEmpty := by
  decide

example : formalCheck string .presentEmpty != formalCheck string .empty := by
  decide

example :
    observeCell .validation (formalCheck string .presentEmpty) = .empty ∧
      observeCell .computation (formalCheck string .presentEmpty) = .empty := by
  decide

example : observeCell .validation requiredEmpty = .unknown .required := by
  decide

example : observeCell .computation requiredEmpty = .empty := by
  decide

example : observeCell .validation (formalCheck optionalNumber (.rejected .malformed)) =
    .unknown .malformed := by
  decide

example : observeCell .computation (formalCheck optionalNumber (.rejected .malformed)) =
    .poison .malformed := by
  decide

example : formalCheck confirm (.parsed (.conf false)) =
    { rawPresent := true, parsed := none, findings := [.malformed] } := by
  decide

/- An already-decoded temporal payload is admitted under the declaration whose **component set**
   names its family. For an ordinary declaration that is also its declared kind. -/
example :
    let instant : Instant := { epochMillis := 100999 }
    formalCheck date (.parsed (temporalValue .date instant)) =
        { rawPresent := true
          parsed := some (temporalValue .date instant)
          findings := [] } ∧
      formalCheck date (.parsed (temporalValue .dateTime instant)) =
        { rawPresent := true
          parsed := none
          findings := [.malformed] } := by
  decide

/- **The declared kind carries no part of the rule, measured in both directions.** A DATE
   declaration at a clock format admits a time payload and refuses a date one; a TIME declaration at
   a date format does the exact opposite. Each kind therefore appears on both sides of both outcomes,
   which is what rules out reading the admitted set off the kind
   ([checkpoint](../../docs/SOURCES.md#src-temporal-value-family-is-the-formats-not-the-kinds)).
   Before this correction both cross rows were malformed, so a cell the Kernel stores and compares
   read as unavailable to every consumer — a wrong value rather than a wrong diagnostic. -/
example :
    let instant : Instant := { epochMillis := 100999 }
    (formalCheck dateAtClockFormat (.parsed (temporalValue .time instant))).parsed =
        some (temporalValue .time instant) ∧
      (formalCheck dateAtClockFormat
        (.parsed (temporalValue .date instant))).findings = [.malformed] ∧
      (formalCheck timeAtDateFormat (.parsed (temporalValue .date instant))).parsed =
        some (temporalValue .date instant) ∧
      (formalCheck timeAtDateFormat
        (.parsed (temporalValue .time instant))).findings = [.malformed] := by
  decide

/- The DateTime family is the third answer rather than a permissive one: only a set naming both
   families admits a DateTime payload, and it refuses each single-family payload. -/
example :
    let instant : Instant := { epochMillis := 100999 }
    let allComponents : TemporalComponents :=
      { year := true, month := true, day := true,
        hour := true, minute := true, second := true }
    let dateTimePolicy : FieldPolicy :=
      { kind := .temporal .date allComponents }
    (formalCheck dateTimePolicy (.parsed (temporalValue .dateTime instant))).parsed =
        some (temporalValue .dateTime instant) ∧
      (formalCheck dateTimePolicy
        (.parsed (temporalValue .date instant))).findings = [.malformed] ∧
      (formalCheck dateTimePolicy
        (.parsed (temporalValue .time instant))).findings = [.malformed] := by
  decide

/- An already-decoded DateRange is admitted only under the distinct DateRange declaration kind. -/
example :
    let instant : Instant := { epochMillis := 100999 }
    formalCheck dateRange (.parsed (.dateRange dateRangeValue)) =
        { rawPresent := true
          parsed := some (.dateRange dateRangeValue)
          findings := [] } ∧
      formalCheck dateRange (.parsed (temporalValue .date instant)) =
        { rawPresent := true
          parsed := none
          findings := [.malformed] } ∧
      formalCheck date (.parsed (.dateRange dateRangeValue)) =
        { rawPresent := true
          parsed := none
          findings := [.malformed] } := by
  decide

/- One heterogeneous runtime domain retains temporal kind independently of exact instant identity. -/
example :
    let instant : Instant := { epochMillis := 100999 }
    (temporalValue .date instant != temporalValue .time instant) ∧
      (temporalValue .date instant != temporalValue .dateTime instant) ∧
      (temporalValue .time instant != temporalValue .dateTime instant) ∧
      (temporalValue .date instant =
        temporalValue .date { epochMillis := 100999 }) := by
  decide

/- The shared checked boundary remains generic for proof-bearing parser values before their admitted runtime projection into `Value`. -/
example (value : Nat) :
    observeCell .validation
      ({ rawPresent := true, parsed := some value, findings := [] } : CheckedCell Nat) =
        (.value value : CellObservation Nat) := by
  rfl

/- Typed present-empty cells and formal findings use the same phase projection. -/
example :
    observeCell .validation
        ({ rawPresent := true, parsed := none, findings := [] } : CheckedCell Nat) =
          (.empty : CellObservation Nat) ∧
      observeCell .computation
        ({ rawPresent := true, parsed := none, findings := [.malformed] } : CheckedCell Nat) =
          (.poison .malformed : CellObservation Nat) := by
  decide

/- An already-admitted typed parser result retains the same placement and rejection states as scalar ingestion. -/
example :
    checkAdmittedRawCell (.parsed 7 : RawCell Nat) =
        ({ rawPresent := true, parsed := some 7, findings := [] } : CheckedCell Nat) ∧
      checkAdmittedRawCell (.empty : RawCell Nat) =
        ({ rawPresent := false, parsed := none, findings := [] } : CheckedCell Nat) ∧
      checkAdmittedRawCell (.rejected .declaredConstraint : RawCell Nat) =
        ({ rawPresent := true
           parsed := none
           findings := [.declaredConstraint] } : CheckedCell Nat) := by
  decide

end A12Kernel.Conformance.Observation
