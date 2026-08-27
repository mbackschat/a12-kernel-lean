import A12Kernel.Elaboration.ValueAsDateTimeExtraction
import A12Kernel.Semantics.BerlinLegacyCalendarArithmetic

/-! # Checked DateTime calendar-day shifts

This capsule evaluates direct and bounded recursively composed nonrepeatable
`AddDays(DateTime, Number)` forms under UTC/GMT and the pinned Berlin profile. It reuses
the shared checked DateTime source and numeric amount boundary, but applies a calendar
`DAY_OF_MONTH` mutation rather than elapsed sub-day arithmetic. The source exact instant
is decoded under the selected profile before the mutation, and the result retains the
landing label, exact instant, milliseconds, and omission provenance. One such result can
feed one further day shift without label reconstruction. The reached-result step is also
reused by the separate bounded elapsed-sub-day-then-calendar-day owner.

DateTime `AddMonths` and `AddYears`, wider recursion, other model zones, repeatable
placement, and dynamic target storage remain outside.
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

/-- One checked model-zone profile and numeric amount for calendar-day shifting this
    execution's explicit `World.now`. -/
structure CheckedNowDateTimeDayShift (model : FlatModel) where
  profile : ModelZone.ConcreteProfile
  profileMatches :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId = some profile
  amount : CheckedTemporalShiftAmount model

/-- Check one ordinary complete-DateTime field and checked numeric amount for the
    calendar-day operation. Month/year DateTime operations have no constructor. -/
def elaborateDateTimeDayShift
    (model : FlatModel) (sourceField : FieldId)
    (amount : CheckedTemporalShiftAmount model) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedDateTimeDayShift model) :=
  elaborateDateTimeNumericShiftSource model sourceField amount

/-- Check a dynamic calendar-day shift without sampling its execution world. -/
def elaborateNowDateTimeDayShift
    (model : FlatModel) (amount : CheckedTemporalShiftAmount model) :
    Except ValueAsDateTimeExtractionElabError
      (CheckedNowDateTimeDayShift model) :=
  match hProfile : ModelZone.ConcreteProfile.ofId? model.timeZoneId with
  | some profile => pure { profile, profileMatches := hProfile, amount }
  | none => throw (.unsupportedZone model.timeZoneId)

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

/-- Apply one reached numeric amount under a certified concrete profile. Arithmetic
    domain failure produces no value; a reached value uses Java signed-32-bit narrowing
    and retains directional fillability as DateTime omission provenance. -/
def applyProfileAmount (profile : ModelZone.ConcreteProfile)
    (sourceLocal : LocalDateTime) (sourceInstant : Instant) :
    NumericArithmeticOutcome →
      Except DateTimeDayShiftFault ValueAsDateTimeResult
  | .notEvaluated => pure (.noValue false)
  | .value value fillability =>
      let offset := temporalShiftAmountToInt32 value
      let notGiven := fillability.canGrow || fillability.canShrink
      if offset = 0 then
        pure (.value sourceLocal sourceInstant notGiven)
      else
        let landing :=
          match profile with
          | .utc => utcLanding? sourceLocal sourceInstant offset
          | .europeBerlin =>
              EuropeBerlinLegacyProfile.calendarDayLanding?
                sourceLocal sourceInstant offset
        match landing with
        | some (shifted, shiftedInstant) =>
            pure (.value shifted shiftedInstant notGiven)
        | none => throw (.landingUnavailable sourceInstant offset)

/-- Apply one reached numeric amount to the exact DateTime source through the profile
    selected by this checked field-backed carrier. -/
def applyAmount (checked : CheckedDateTimeDayShift model)
    (sourceLocal : LocalDateTime) (sourceInstant : Instant) :
    NumericArithmeticOutcome →
      Except DateTimeDayShiftFault ValueAsDateTimeResult
  | outcome =>
      applyProfileAmount checked.profile sourceLocal sourceInstant outcome

/-- Apply an outer amount to one already-evaluated exact DateTime result under a
    certified profile. A concrete inner value retains its omission provenance. -/
def applyProfileResultAmount (profile : ModelZone.ConcreteProfile)
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
          match applyProfileAmount profile sourceLocal sourceInstant
              (.value value fillability) with
          | .error error => .error error
          | .ok result => .ok (result.inheritNotGiven notGiven)
      | .nonRelevant => pure .nonRelevant
      | .unavailable cause => pure (.unavailable cause)

/-- Apply an outer amount through the profile selected by this checked field-backed
    carrier. -/
def applyResultAmount (checked : CheckedDateTimeDayShift model)
    (source : ValueAsDateTimeResult) :
    NumericArithmeticOutcome →
      Except DateTimeDayShiftFault ValueAsDateTimeResult
  | outcome =>
      applyProfileResultAmount checked.profile source outcome

/-- Classify one reached DateTime cell before reading its numeric amount. A formal
    source stops; an empty source still reaches the amount and remains not-given. -/
def evaluateObservation (profile : ModelZone.ConcreteProfile)
    (sourceField : FieldId) (observation : CellObservation Value)
    (readAmount : Unit →
      Except Fault
        (Except NumericValidationUnavailable NumericArithmeticOutcome))
    (mapFault : DateTimeDayShiftFault → Fault) :
    Except Fault ValueAsDateTimeResult := do
  match observation with
  | .empty =>
      match ← readAmount () with
      | .error (.formal cause) => pure (.unavailable cause)
      | .error unavailable => throw (mapFault (.amountUnavailable unavailable))
      | .ok _ => pure (.noValue true)
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.temporal (.dateTime instant _ _ _)) =>
      match profile.localDateTime? instant with
      | none => throw (mapFault (.sourceOutsideProfile instant))
      | some sourceLocal =>
          match ← readAmount () with
          | .error (.formal cause) => pure (.unavailable cause)
          | .error unavailable => throw (mapFault (.amountUnavailable unavailable))
          | .ok outcome =>
              applyProfileAmount profile sourceLocal instant outcome
                |>.mapError mapFault
  | .value _ => throw (mapFault (.sourcePayloadMismatch sourceField))

/-- Classify one reached DateTime cell before reading its numeric amount. A formal
    source stops; an empty source still reaches the amount and remains not-given. -/
def evaluateCell (checked : CheckedDateTimeDayShift model)
    (phase : Phase) (input : CheckedDocument model)
    (cell : CheckedCell) :
    Except DateTimeDayShiftFault ValueAsDateTimeResult :=
  evaluateObservation checked.profile checked.source.id
    (observeCell phase cell)
    (fun _ => checked.amount.read phase input |>.mapError .document)
    id

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

/-- Read and apply one checked day amount to an already evaluated exact DateTime result
    under a certified profile. A reached formal cause stops before this read;
    cause-free no-value still reaches it. -/
def evaluateProfileResult (profile : ModelZone.ConcreteProfile)
    (amount : CheckedTemporalShiftAmount model)
    (source : ValueAsDateTimeResult)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateTimeDayShiftFault ValueAsDateTimeResult :=
  match source with
  | .unavailable cause => .ok (.unavailable cause)
  | source =>
      match amount.read phase input with
      | .error error => .error (.document error)
      | .ok (.error (.formal cause)) => .ok (.unavailable cause)
      | .ok (.error unavailable) => .error (.amountUnavailable unavailable)
      | .ok (.ok outcome) => applyProfileResultAmount profile source outcome

/-- Read and apply the next day amount through this checked field-backed carrier. -/
def evaluateResult (checked : CheckedDateTimeDayShift model)
    (source : ValueAsDateTimeResult)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateTimeDayShiftFault ValueAsDateTimeResult :=
  evaluateProfileResult checked.profile checked.amount source phase input

/-- Feed one exact DateTime day result into a further generated `AddDays`. The inner
    operation runs before the outer amount; a formal inner result stops that read. -/
def evaluateThen (checked : CheckedDateTimeDayShift model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model) :
    Except DateTimeDayShiftFault ValueAsDateTimeResult :=
  match checked.evaluate phase input with
  | .error error => .error error
  | .ok source =>
      CheckedDateTimeDayShift.evaluateResult
        ({ checked with amount := nextAmount } :
          CheckedDateTimeDayShift model)
        source phase input

end CheckedDateTimeDayShift

namespace CheckedNowDateTimeDayShift

/-- Decode this execution's exact `World.now`, then apply the checked calendar-day
    amount under the model-owned profile. No world value is sampled during checking. -/
def evaluate (checked : CheckedNowDateTimeDayShift model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except DateTimeDayShiftFault ValueAsDateTimeResult :=
  match checked.profile.localDateTime? world.now with
  | none => .error (.sourceOutsideProfile world.now)
  | some sourceLocal =>
      CheckedDateTimeDayShift.evaluateProfileResult
        checked.profile checked.amount
        (.value sourceLocal world.now false) phase input

/-- Feed this execution's exact dynamic day result into one further generated
    `AddDays`. The inner operation runs before the outer amount. -/
def evaluateThen (checked : CheckedNowDateTimeDayShift model)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (world : World) (input : CheckedDocument model) :
    Except DateTimeDayShiftFault ValueAsDateTimeResult :=
  match checked.evaluate phase world input with
  | .error error => .error error
  | .ok source =>
      CheckedDateTimeDayShift.evaluateProfileResult
        checked.profile nextAmount source phase input

end CheckedNowDateTimeDayShift

end A12Kernel
