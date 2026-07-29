import A12Kernel.Elaboration.ConstructedDateEvaluation

/-! # Checked constructed-Date shifts

This capsule evaluates one checked constructed Date followed by one or two generated
calendar shifts. Fresh Date construction resolves a wall label exactly once. A nested
shift consumes the inner result's exact instant directly, so repeated-hour identity is
never lost through label reconstruction.

UTC/GMT retain the carried legacy-hybrid date identity. Pinned Berlin decodes each
continuation source from its exact instant before applying the unit-specific field
mutation. A general temporal-expression tree, DateTime operands, target storage, other
model zones, and shift-to-difference composition remain outside.
-/

namespace A12Kernel

/-- Reason-bearing checked shift result retaining both exact instant and local Date parts. -/
inductive ConstructedDateShiftResult where
  | noValue (notGiven : Bool)
  | value (instant : Instant) (parts : DateParts) (notGiven : Bool)
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

/-- Structural failure outside constructed-Date and numeric-operand reason semantics. -/
inductive ConstructedDateShiftFault where
  | source (error : ConstructedDateEvaluationFault)
  | amountDocument (error : CheckedDocumentError)
  | amountUnavailable (error : NumericValidationUnavailable)
  | landingUnavailable
      (unit : DateShiftUnit) (source : DateParts) (offset : Int)
  deriving Repr, DecidableEq

/-- One checked constructed-Date source, calendar unit, and shared checked shift amount. -/
structure CheckedConstructedDateShift (model : FlatModel) where
  source : CheckedConstructedDateComponents model
  unit : DateShiftUnit
  amount : CheckedTemporalShiftAmount model

namespace CheckedConstructedDateShift

/-- Whether the already-evaluated constructed source carries omission provenance into the shift helper. -/
def sourceNotGiven : ConstructedDateObservation → Bool
  | .resolved .incomplete => true
  | .resolved (.real _) => false
  | .resolved .unreal => false
  | .resolved .unknown => false
  | .unavailable _ => false

private def shiftResolved? (unit : DateShiftUnit)
    (result : DateConstructionResult) (offset : Int) :
    Option DateConstructionResult :=
  match unit with
  | .days => result.addLegacyDays? offset
  | .months => result.addLegacyMonths? offset
  | .years => result.addLegacyYears? offset

/-- Apply one real shift to an exact already-resolved source. UTC/GMT retain the
    carried legacy-hybrid parts; Berlin decodes the source wall label from the exact
    instant before applying its unit-specific field mutation. -/
private def applyResolvedRealAmount
    (checked : CheckedConstructedDateShift model)
    (sourceInstant : Instant) (parts : DateParts)
    (offset : Int) (notGiven : Bool) :
    Except ConstructedDateShiftFault ConstructedDateShiftResult :=
  match checked.source.profile with
  | .utc =>
      if offset = 0 then
        pure (.value sourceInstant parts notGiven)
      else
        match shiftResolved? checked.unit (.real parts) offset with
        | some (.real shifted) =>
            match DateParts.LegacyHybrid.midnightInstant? shifted with
            | some instant => pure (.value instant shifted notGiven)
            | none => throw (.landingUnavailable checked.unit parts offset)
        | some .incomplete => pure (.noValue notGiven)
        | some .unreal => pure (.noValue notGiven)
        | some .unknown => pure (.noValue notGiven)
        | none => throw (.landingUnavailable checked.unit parts offset)
  | .europeBerlin =>
      match checked.source.profile.localDateTime? sourceInstant with
      | none => throw (.landingUnavailable checked.unit parts offset)
      | some sourceLocal =>
          let landing :=
            match checked.unit with
            | .days =>
                EuropeBerlinLegacyProfile.calendarDayLanding?
                  sourceLocal sourceInstant offset
            | .months =>
                EuropeBerlinLegacyProfile.calendarMonthLanding?
                  sourceLocal sourceInstant offset
            | .years =>
                EuropeBerlinLegacyProfile.calendarYearLanding?
                  sourceLocal sourceInstant offset
          match landing with
          | none =>
              throw (.landingUnavailable checked.unit parts offset)
          | some (shifted, shiftedInstant) =>
              pure (.value shiftedInstant shifted.date.civil.parts notGiven)

/-- Apply one real shift to a freshly constructed Date. Label resolution happens
    exactly once here; recursive continuations use `applyResolvedRealAmount`
    directly and therefore retain overlap identity. -/
private def applyRealAmount (checked : CheckedConstructedDateShift model)
    (parts : DateParts) (offset : Int) (notGiven : Bool) :
    Except ConstructedDateShiftFault ConstructedDateShiftResult := do
  let sourceInstant ←
    match checked.source.profile with
    | .utc =>
        match DateParts.LegacyHybrid.midnightInstant? parts with
        | some instant => pure instant
        | none => throw (.landingUnavailable checked.unit parts offset)
    | .europeBerlin =>
        match LocalDateTime.ofYmdHms?
            parts.year parts.month parts.day 0 0 0 with
        | none => throw (.landingUnavailable checked.unit parts offset)
        | some sourceLocal =>
            match checked.source.profile.resolveLocal? sourceLocal with
            | some instant => pure instant
            | none => throw (.landingUnavailable checked.unit parts offset)
  checked.applyResolvedRealAmount sourceInstant parts offset notGiven

/-- Apply an already reached numeric amount without losing missing provenance or reinterpreting arithmetic domain failure as zero. -/
def applyAmount (checked : CheckedConstructedDateShift model)
    (source : ConstructedDateObservation) :
    NumericArithmeticOutcome →
      Except ConstructedDateShiftFault ConstructedDateShiftResult
  | .notEvaluated => pure (.noValue (sourceNotGiven source))
  | .value value fillability =>
      let notGiven :=
        sourceNotGiven source || fillability.canGrow || fillability.canShrink
      match source with
      | .unavailable cause => pure (.unavailable cause)
      | .resolved (.real parts) =>
          let offset := temporalShiftAmountToInt32 value
          checked.applyRealAmount parts offset notGiven
      | .resolved .incomplete => pure (.noValue notGiven)
      | .resolved .unreal => pure (.noValue notGiven)
      | .resolved .unknown => pure (.noValue notGiven)

/-- Apply an outer amount to one already-evaluated shift result. Its exact instant
    is the next calendar source; it is never reconstructed from the carried date
    parts. -/
def applyResultAmount (checked : CheckedConstructedDateShift model)
    (source : ConstructedDateShiftResult) :
    NumericArithmeticOutcome →
      Except ConstructedDateShiftFault ConstructedDateShiftResult
  | .notEvaluated =>
      match source with
      | .noValue notGiven | .value _ _ notGiven => pure (.noValue notGiven)
      | .unavailable cause => pure (.unavailable cause)
  | .value value fillability =>
      match source with
      | .unavailable cause => pure (.unavailable cause)
      | .noValue sourceNotGiven =>
          pure (.noValue
            (sourceNotGiven || fillability.canGrow || fillability.canShrink))
      | .value sourceInstant parts sourceNotGiven =>
          let notGiven :=
            sourceNotGiven || fillability.canGrow || fillability.canShrink
          let offset := temporalShiftAmountToInt32 value
          checked.applyResolvedRealAmount
            sourceInstant parts offset notGiven

/-- Evaluate the constructed Date before its amount with one explicit optional world, matching generated Java argument order. A reached source cause therefore stops before the amount; a cause-free no-value source still reaches it. -/
def evaluate (checked : CheckedConstructedDateShift model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateShiftFault ConstructedDateShiftResult :=
  match checked.source.evaluate phase input world with
  | .error error => .error (.source error)
  | .ok (.unavailable cause) => .ok (.unavailable cause)
  | .ok source =>
      match checked.amount.read phase input with
      | .error error => .error (.amountDocument error)
      | .ok (.error (.formal cause)) => .ok (.unavailable cause)
      | .ok (.error unavailable) => .error (.amountUnavailable unavailable)
      | .ok (.ok outcome) => checked.applyAmount source outcome

/-- Evaluate one checked shift and feed its exact result directly into one further
    checked calendar mutation. This is the smallest generated nested-call boundary:
    the inner operation runs before the outer amount, and a reached inner formal
    cause stops before that amount is read. -/
def evaluateThen (checked : CheckedConstructedDateShift model)
    (nextUnit : DateShiftUnit)
    (nextAmount : CheckedTemporalShiftAmount model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateShiftFault ConstructedDateShiftResult :=
  match checked.evaluate phase input world with
  | .error error => .error error
  | .ok (.unavailable cause) => .ok (.unavailable cause)
  | .ok source =>
      match nextAmount.read phase input with
      | .error error => .error (.amountDocument error)
      | .ok (.error (.formal cause)) => .ok (.unavailable cause)
      | .ok (.error unavailable) => .error (.amountUnavailable unavailable)
      | .ok (.ok outcome) =>
          let next : CheckedConstructedDateShift model := {
            checked with
            unit := nextUnit
            amount := nextAmount
          }
          next.applyResultAmount source outcome

end CheckedConstructedDateShift

end A12Kernel
