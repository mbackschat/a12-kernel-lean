import A12Kernel.Elaboration.ValueAsDateTimeExtraction
import A12Kernel.Semantics.BerlinLegacyCalendarArithmetic

/-! # Checked DateTime calendar-day shifts

This capsule evaluates direct and bounded recursively composed nonrepeatable
`AddDays(DateTime, Number)` forms under UTC/GMT and the pinned Berlin profile. It reuses
the shared checked DateTime source and numeric amount boundary, but applies a calendar
`DAY_OF_MONTH` mutation rather than elapsed sub-day arithmetic. The source exact instant
is decoded under the selected profile before the mutation, and the result retains the
landing label, exact instant, milliseconds, and omission provenance. One such result can
feed one further day shift without label reconstruction.

DateTime `AddMonths` and `AddYears`, dynamic `Now`, wider recursion, other model zones,
repeatable placement, and target storage remain outside.
-/

namespace A12Kernel

/-- Structural failure outside the reason-bearing DateTime day-shift result. -/
inductive DateTimeDayShiftFault where
  | document (error : CheckedDocumentError)
  | amountUnavailable (error : NumericValidationUnavailable)
  | sourcePayloadMismatch (field : FieldId)
  | sourceOutsideProfile (instant : Instant)
  | landingUnavailable (source : Instant) (offset : Int)
  deriving Repr, DecidableEq

/-- The shared checked DateTime/numeric source specialized by type to calendar days. -/
abbrev CheckedDateTimeDayShift :=
  CheckedDateTimeNumericShiftSource

/-- Check one ordinary complete-DateTime field and checked numeric amount for the
    calendar-day operation. Month/year DateTime operations have no constructor. -/
def elaborateDateTimeDayShift
    (model : FlatModel) (sourceField : FieldId)
    (amount : CheckedTemporalShiftAmount model) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedDateTimeDayShift model) :=
  elaborateDateTimeNumericShiftSource model sourceField amount

namespace CheckedDateTimeDayShift

/-- Apply one UTC calendar-day mutation, preserving the selected exact instant for zero
    and retaining its millisecond remainder for a nonzero landing. -/
def utcLanding? (sourceLocal : LocalDateTime)
    (sourceInstant : Instant) (offset : Int) :
    Option (LocalDateTime × Instant) := do
  if offset = 0 then
    pure (sourceLocal, sourceInstant)
  else
    let nextDate ← sourceLocal.date.addDays? offset
    let next : LocalDateTime := {
      date := nextDate
      time := sourceLocal.time
    }
    pure (next, {
      epochMillis :=
        next.resolveUtc.epochMillis + sourceInstant.epochMillis % 1000
    })

/-- Apply one reached numeric amount to the exact DateTime source. Arithmetic domain
    failure produces no value; a reached value uses Java signed-32-bit narrowing and
    retains directional fillability as DateTime omission provenance. -/
def applyAmount (checked : CheckedDateTimeDayShift model)
    (sourceLocal : LocalDateTime) (sourceInstant : Instant) :
    NumericArithmeticOutcome →
      Except DateTimeDayShiftFault ValueAsDateTimeResult
  | .notEvaluated => pure (.noValue false)
  | .value value fillability =>
      let offset := temporalShiftAmountToInt32 value
      let notGiven := fillability.canGrow || fillability.canShrink
      let landing :=
        match checked.profile with
        | .utc => utcLanding? sourceLocal sourceInstant offset
        | .europeBerlin =>
            EuropeBerlinLegacyProfile.calendarDayLanding?
              sourceLocal sourceInstant offset
      match landing with
      | some (shifted, shiftedInstant) =>
          pure (.value shifted shiftedInstant notGiven)
      | none => throw (.landingUnavailable sourceInstant offset)

/-- Apply an outer amount to one already-evaluated DateTime day result. A concrete
    inner value remains the exact calendar source and retains its omission provenance. -/
def applyResultAmount (checked : CheckedDateTimeDayShift model)
    (source : ValueAsDateTimeResult) :
    NumericArithmeticOutcome →
      Except DateTimeDayShiftFault ValueAsDateTimeResult
  | .notEvaluated =>
      match source with
      | .noValue notGiven | .value _ _ notGiven => pure (.noValue notGiven)
      | .nonRelevant => pure .nonRelevant
      | .unavailable cause => pure (.unavailable cause)
  | .value value fillability =>
      match source with
      | .noValue notGiven =>
          pure (.noValue
            (notGiven || fillability.canGrow || fillability.canShrink))
      | .value sourceLocal sourceInstant notGiven =>
          match checked.applyAmount sourceLocal sourceInstant
              (.value value fillability) with
          | .error error => .error error
          | .ok result => .ok (result.inheritNotGiven notGiven)
      | .nonRelevant => pure .nonRelevant
      | .unavailable cause => pure (.unavailable cause)

/-- Classify one reached DateTime cell before reading its numeric amount. A formal
    source stops; an empty source still reaches the amount and remains not-given. -/
def evaluateCell (checked : CheckedDateTimeDayShift model)
    (phase : Phase) (input : CheckedDocument model)
    (cell : CheckedCell) :
    Except DateTimeDayShiftFault ValueAsDateTimeResult := do
  match observeCell phase cell with
  | .empty =>
      match ← checked.amount.read phase input |>.mapError .document with
      | .error (.formal cause) => pure (.unavailable cause)
      | .error unavailable => throw (.amountUnavailable unavailable)
      | .ok _ => pure (.noValue true)
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.temporal (.dateTime instant _ _ _)) =>
      match checked.profile.localDateTime? instant with
      | none => throw (.sourceOutsideProfile instant)
      | some sourceLocal =>
          match ← checked.amount.read phase input |>.mapError .document with
          | .error (.formal cause) => pure (.unavailable cause)
          | .error unavailable => throw (.amountUnavailable unavailable)
          | .ok outcome => checked.applyAmount sourceLocal instant outcome
  | .value _ => throw (.sourcePayloadMismatch checked.source.id)

/-- Read the checked DateTime before its numeric amount, then delegate the reached cell
    to the source-before-amount classifier. -/
def evaluate (checked : CheckedDateTimeDayShift model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateTimeDayShiftFault ValueAsDateTimeResult := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.evaluateCell phase input cell

/-- Feed one exact DateTime day result into a further generated `AddDays`. The inner
    operation runs before the outer amount; a formal inner result stops that read. -/
def evaluateThen (checked : CheckedDateTimeDayShift model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateTimeDayShiftFault ValueAsDateTimeResult :=
  match checked.evaluate phase input with
  | .error error => .error error
  | .ok (.unavailable cause) => .ok (.unavailable cause)
  | .ok source =>
      match nextAmount.read phase input with
      | .error error => .error (.document error)
      | .ok (.error (.formal cause)) => .ok (.unavailable cause)
      | .ok (.error unavailable) => .error (.amountUnavailable unavailable)
      | .ok (.ok outcome) => checked.applyResultAmount source outcome

end CheckedDateTimeDayShift

end A12Kernel
