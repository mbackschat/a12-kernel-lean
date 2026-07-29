import A12Kernel.Elaboration.ConstructedDateComponents
import A12Kernel.Elaboration.TemporalShiftAmount
import A12Kernel.Semantics.BaseYearDateSource
import A12Kernel.Semantics.ConstructedDateDay
import A12Kernel.Semantics.DateTimeDayDifference

/-! # Checked constructed-Date execution

This capsule evaluates one certified direct constructed Date in generated component order. Number fields, pattern-backed String fields, the complete-Year `yyyy` Date field, and direct Date/DateTime extractors read the immutable checked document; constants and direct/range-selected Base-Year extractors are fixed inputs; and `Today`/`Now` resolve only from the execution's explicit optional `World`. The two-argument form uses the model Base Year, and the four-argument form reads Century before Short-Year and combines them only when both are present. It wraps the existing cause-free construction result only to retain the first reached formal cause. UTC/GMT retain the established hybrid-calendar reality; pinned Berlin additionally requires a post-floor local-midnight label admitted by its selected profile.

Checked shifts retain exact landing instants as well as Date parts. UTC/GMT use the complete hybrid owner; pinned Berlin admits signed day, month, and year additions after the checked Date floor while preserving each `GregorianCalendar` field mutation's distinct overlap policy. Differences remain UTC/GMT. Source components are evaluated before the amount; exact formal causes, missing provenance, arithmetic domain failure, and Java signed-32-bit narrowing remain distinguishable. Berlin differences, Berlin's pre-floor hybrid identity, the extensible-enumeration String alternative, other recursive extractor operands, another model zone, repeatable placement, targets, and a general temporal-expression tree remain outside.
-/

namespace A12Kernel

/-- Structural failure outside Date-construction reason semantics. -/
inductive ConstructedDateEvaluationFault where
  | document (error : CheckedDocumentError)
  | payloadKind (field : FieldId)
  | stringNotConvertible (field : FieldId) (value : String)
  | dateYearStoredMissing (field : FieldId)
  | dateYearNotConvertible (field : FieldId) (value : String)
  | nonIntegralPayload (field : FieldId) (value : Rat)
  | todayWorldRequired
  | todayUnavailable (zoneId : String)
  | nowWorldRequired
  | nowUnavailable (zoneId : String)
  | profileDateUnsupported (zoneId : String) (parts : DateParts)
  deriving Repr, DecidableEq

/-- A checked component before cause-free construction classification. -/
inductive CheckedConstructedDateComponent where
  | value (amount : Int)
  | empty
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

namespace CheckedConstructedDateNumberField

/-- Preserve empty and formal state while rejecting a forged fractional or non-Number payload. -/
def classify (checked : CheckedConstructedDateNumberField model)
    (observation : CellObservation Value) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.num value) =>
      if value.den = 1 then
        pure (.value value.num)
      else
        throw (.nonIntegralPayload checked.source.id value)
  | .value _ => throw (.payloadKind checked.source.id)

/-- Read one certified scalar component through the immutable checked document. -/
def read (checked : CheckedConstructedDateNumberField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedConstructedDateNumberField

namespace CheckedConstructedDateStringField

/-- Convert one already checked digit String through the shared ASCII-natural parser while preserving empty and formal state. -/
def classify (checked : CheckedConstructedDateStringField model)
    (observation : CellObservation Value) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.str value) =>
      match parseAsciiNatural? value with
      | some amount => pure (.value amount)
      | none => throw (.stringNotConvertible checked.source.id value)
  | .value _ => throw (.payloadKind checked.source.id)

/-- Read one certified scalar String component through the immutable checked document. -/
def read (checked : CheckedConstructedDateStringField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedConstructedDateStringField

namespace CheckedConstructedDateYearField

/-- Convert the exact stored `yyyy` text while using the checked cell only for empty, formal, and payload-kind state. This is intentionally distinct from `YearFromDate`, which projects the decoded temporal value. -/
def classify (checked : CheckedConstructedDateYearField model)
    (observation : CellObservation Value) (stored : Option String) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.temporal value) =>
      if value.kind != .date then
        throw (.payloadKind checked.source.id)
      else
        match stored with
        | none => throw (.dateYearStoredMissing checked.source.id)
        | some text =>
            match parseAsciiNatural? text with
            | some amount => pure (.value amount)
            | none => throw (.dateYearNotConvertible checked.source.id text)
  | .value _ => throw (.payloadKind checked.source.id)

/-- Read one certified `yyyy` Date component from the immutable checked cell and its retained exact stored text. -/
def read (checked : CheckedConstructedDateYearField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent := do
  let address : CellAddr := {
    field := checked.source.id
    path := []
  }
  let cell ← input.read address |>.mapError .document
  checked.classify (observeCell phase cell)
    (input.source.toDocument.rawCells address)

end CheckedConstructedDateYearField

namespace CheckedConstructedDateExtractorField

/-- Preserve empty and formal state while projecting the certified calendar component from a Date or DateTime payload. -/
def classify (checked : CheckedConstructedDateExtractorField model)
    (observation : CellObservation Value) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match observation with
  | .empty => pure .empty
  | .unknown cause | .poison cause => pure (.unavailable cause)
  | .value (.temporal value) =>
      if value.kind != checked.source.kind then
        throw (.payloadKind checked.source.id)
      else
        match value.dateParts? with
        | none => throw (.payloadKind checked.source.id)
        | some parts =>
            let amount := checked.part.extract parts
            if amount.den = 1 then
              pure (.value amount.num)
            else
              throw (.nonIntegralPayload checked.source.id amount)
  | .value _ => throw (.payloadKind checked.source.id)

/-- Read one certified scalar Date component through the immutable checked document. -/
def read (checked : CheckedConstructedDateExtractorField model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent := do
  let cell ← input.read {
    field := checked.source.id
    path := []
  } |>.mapError .document
  checked.classify (observeCell phase cell)

end CheckedConstructedDateExtractorField

namespace CheckedConstructedDateBaseYearExtractor

/-- Project the matching component from the configured direct or range-selected Base-Year Date source without consulting document state. `baseYearDateSourceNumericPart` owns that source interpretation; its normalized rational numerator is exact for every admitted component. -/
def read (checked : CheckedConstructedDateBaseYearExtractor model)
    (_phase : Phase) (_input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  pure (.value
    (baseYearDateSourceNumericPart
      checked.year checked.source checked.part).num)

end CheckedConstructedDateBaseYearExtractor

namespace CheckedConstructedDatePointInTimeExtractor

/-- Decode one exact instant through the certified profile and project the selected Date
    component, preserving the acquisition-specific structural fault. -/
def project
    (checked : CheckedConstructedDatePointInTimeExtractor model)
    (instant : Instant) (unavailable : ConstructedDateEvaluationFault) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match checked.profile.localDate? instant with
  | none => throw unavailable
  | some date =>
      pure (.value (checked.part.extract date.civil.parts).num)

/-- Resolve the selected point in time from the supplied execution world, then project
    the matching local calendar component through the model-certified zone profile.
    `Today` asks the world for model-zone midnight; `Now` keeps its exact instant. -/
def read (checked : CheckedConstructedDatePointInTimeExtractor model)
    (world : Option World) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match world with
  | none =>
      match checked.point with
      | .today => throw .todayWorldRequired
      | .now => throw .nowWorldRequired
  | some world =>
      match checked.point with
      | .today =>
          match world.today? model.timeZoneId with
          | none => throw (.todayUnavailable model.timeZoneId)
          | some instant =>
              checked.project instant (.todayUnavailable model.timeZoneId)
      | .now =>
          checked.project world.now (.nowUnavailable model.timeZoneId)

end CheckedConstructedDatePointInTimeExtractor

namespace CheckedConstructedDateSource

/-- Read one component with the caller's explicit optional execution world. -/
def read (checked : CheckedConstructedDateSource model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match checked with
  | .numberField source => source.read phase input
  | .stringField source => source.read phase input
  | .dateYearField source => source.read phase input
  | .constant value => pure (.value value)
  | .extractor source => source.read phase input
  | .baseYearExtractor source => source.read phase input
  | .pointInTimeExtractor source => source.read world

end CheckedConstructedDateSource

namespace CheckedConstructedDateYear

/-- Read one checked year form with the caller's explicit optional world. Split-year evaluation preserves Century-before-Short-Year formal precedence, while any ordinary empty component keeps the construction incomplete. -/
def read (checked : CheckedConstructedDateYear model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match checked with
  | .complete source => source.read phase input world
  | .baseYear year => pure (.value year)
  | .centuryAndShortYear century shortYear =>
      match century.read phase input world with
      | .error error => .error error
      | .ok (.unavailable cause) => .ok (.unavailable cause)
      | .ok centuryPart =>
          match shortYear.read phase input world with
          | .error error => .error error
          | .ok (.unavailable cause) => .ok (.unavailable cause)
          | .ok shortYearPart =>
              match centuryPart, shortYearPart with
              | .value century, .value shortYear =>
                  .ok (.value (century * 100 + shortYear))
              | _, _ => .ok .empty

end CheckedConstructedDateYear

/-- A cause-preserving checked observation around the existing four-way construction result. -/
inductive ConstructedDateObservation where
  | resolved (result : DateConstructionResult)
  | unavailable (cause : FormalCause)
  deriving Repr, DecidableEq

namespace ConstructedDateObservation

/-- Resolve three cause-free checked components. `none` means empty; formal unavailability is intercepted before this seam, so this constructor cannot produce `.resolved .unknown`. -/
def ofAvailableComponents (day month year : Option Int) :
    ConstructedDateObservation :=
  let availability : Option Int → DateComponentAvailability
    | some _ => .present
    | none => .empty
  let reality := match day, month, year with
    | some day, some month, some year =>
        let parts : DateParts := {
          year
          month := Int.toNat month
          day := Int.toNat day }
        if DateParts.LegacyHybrid.isReal parts then
          .real parts
        else
          .unreal
    | _, _, _ => .unreal
  .resolved (classifyDateConstruction3
    (availability day) (availability month) (availability year) reality)

/-- Project checked `Valid(Date(...))` without discarding a reached formal cause. -/
def validVerdict : ConstructedDateObservation → Except FormalCause Verdict
  | .resolved result => .ok result.validVerdict
  | .unavailable cause => .error cause

/-- Project checked `Invalid(Date(...))` without discarding a reached formal cause. -/
def invalidVerdict : ConstructedDateObservation → Except FormalCause Verdict
  | .resolved result => .ok result.invalidVerdict
  | .unavailable cause => .error cause

/-- Project one checked numeric component through the existing cause-free result family. A forged resolved UNKNOWN remains explicitly cause-free; checked evaluation never produces that branch. -/
def numericPart (observation : ConstructedDateObservation)
    (part : DateNumericPart) :
    Except FormalCause ConstructedDateNumericResult :=
  match observation with
  | .resolved result => .ok (result.numericPart part)
  | .unavailable cause => .error cause

/-- Shift a resolved observation by default-cutover calendar days without losing a formal cause. -/
def addLegacyDays? : ConstructedDateObservation → Int →
    Option ConstructedDateObservation
  | .resolved result, offset => (result.addLegacyDays? offset).map .resolved
  | .unavailable cause, _ => some (.unavailable cause)

/-- Shift a resolved observation by default-cutover calendar months without losing a formal cause. -/
def addLegacyMonths? : ConstructedDateObservation → Int →
    Option ConstructedDateObservation
  | .resolved result, offset => (result.addLegacyMonths? offset).map .resolved
  | .unavailable cause, _ => some (.unavailable cause)

/-- Shift a resolved observation by default-cutover calendar years without losing a formal cause. -/
def addLegacyYears? : ConstructedDateObservation → Int →
    Option ConstructedDateObservation
  | .resolved result, offset => (result.addLegacyYears? offset).map .resolved
  | .unavailable cause, _ => some (.unavailable cause)

end ConstructedDateObservation

namespace CheckedConstructedDateComponents

/-- Decide whether one already hybrid-real Date also exists at local midnight in the
    selected profile. UTC retains the established pre-floor hybrid account; Berlin is
    deliberately bounded to labels admitted by `FullDate` before zone resolution. -/
def profileAcceptsDate (checked : CheckedConstructedDateComponents model)
    (parts : DateParts) :
    Except ConstructedDateEvaluationFault Bool :=
  match checked.profile with
  | .utc => pure true
  | .europeBerlin =>
      match LocalDateTime.ofYmdHms?
          parts.year parts.month parts.day 0 0 0 with
      | none =>
          throw (.profileDateUnsupported model.timeZoneId parts)
      | some dateTime =>
          pure (checked.profile.resolveLocal? dateTime).isSome

/-- Apply the selected profile's local-midnight reality without changing incomplete,
    already-unreal, or formally unavailable construction results. -/
def applyProfileReality (checked : CheckedConstructedDateComponents model) :
    ConstructedDateObservation →
      Except ConstructedDateEvaluationFault ConstructedDateObservation
  | .resolved (.real parts) => do
      if ← checked.profileAcceptsDate parts then
        pure (.resolved (.real parts))
      else
        pure (.resolved .unreal)
  | observation => pure observation

private def availableAmount? : CheckedConstructedDateComponent → Option Int
  | .value amount => some amount
  | .empty | .unavailable _ => none

/-- Read Day, Month, and Year in generated argument order with one caller-supplied optional world. A reached formal component stops before later reads and retains its exact cause. -/
def evaluate (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateEvaluationFault ConstructedDateObservation :=
  match checked.day.read phase input world with
  | .error error => .error error
  | .ok (.unavailable cause) => .ok (.unavailable cause)
  | .ok day =>
      match checked.month.read phase input world with
      | .error error => .error error
      | .ok (.unavailable cause) => .ok (.unavailable cause)
      | .ok month =>
          match checked.year.read phase input world with
          | .error error => .error error
          | .ok (.unavailable cause) => .ok (.unavailable cause)
          | .ok year =>
              checked.applyProfileReality
                (ConstructedDateObservation.ofAvailableComponents
                  (availableAmount? day) (availableAmount? month)
                  (availableAmount? year))

/-- Evaluate checked `Valid(Date(...))` with one explicit optional world, keeping document faults and formal causes in their separate channels. -/
def evaluateValid (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) (world : Option World) :
    Except ConstructedDateEvaluationFault (Except FormalCause Verdict) :=
  (checked.evaluate phase input world).map
    ConstructedDateObservation.validVerdict

/-- Evaluate checked `Invalid(Date(...))` with one explicit optional world, keeping document faults and formal causes in their separate channels. -/
def evaluateInvalid (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) (world : Option World) :
    Except ConstructedDateEvaluationFault (Except FormalCause Verdict) :=
  (checked.evaluate phase input world).map
    ConstructedDateObservation.invalidVerdict

/-- Evaluate one checked Day/Month/Quarter/Year projection with one explicit optional world without adding another numeric result family. -/
def evaluateNumericPart (checked : CheckedConstructedDateComponents model)
    (part : DateNumericPart) (phase : Phase)
    (input : CheckedDocument model) (world : Option World) :
    Except ConstructedDateEvaluationFault
      (Except FormalCause ConstructedDateNumericResult) :=
  (checked.evaluate phase input world).map fun observation =>
    observation.numericPart part

end CheckedConstructedDateComponents

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

/-- Apply one real shift under the selected concrete profile. UTC/GMT use the complete hybrid-calendar owner. Berlin admits signed day, month, and year additions: days retain direction-specific gap/overlap landings, while month and year field mutation select the later overlap instant independently of sign. -/
private def applyRealAmount (checked : CheckedConstructedDateShift model)
    (parts : DateParts) (offset : Int) (notGiven : Bool) :
    Except ConstructedDateShiftFault ConstructedDateShiftResult :=
  match checked.source.profile with
  | .utc =>
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
      match checked.unit with
      | .days =>
          match LocalDateTime.ofYmdHms?
              parts.year parts.month parts.day 0 0 0 with
          | none => throw (.landingUnavailable checked.unit parts offset)
          | some sourceLocal =>
              match checked.source.profile.resolveLocal? sourceLocal with
              | none => throw (.landingUnavailable checked.unit parts offset)
              | some instant =>
                  let landing :=
                    if offset < 0 then
                      EuropeBerlinLegacyProfile.calendarDayLandingBackward?
                        sourceLocal instant offset.natAbs
                    else
                      EuropeBerlinLegacyProfile.calendarDayLanding?
                        sourceLocal instant offset.toNat
                  match landing with
                  | none =>
                      throw (.landingUnavailable checked.unit parts offset)
                  | some (shifted, shiftedInstant) =>
                      pure (.value shiftedInstant
                        shifted.date.civil.parts notGiven)
      | .months =>
          match DateParts.LegacyHybrid.addMonths? parts offset with
          | none =>
              throw (.landingUnavailable checked.unit parts offset)
          | some shifted =>
              match LocalDateTime.ofYmdHms?
                  shifted.year shifted.month shifted.day 0 0 0 with
              | none =>
                  throw (.landingUnavailable checked.unit parts offset)
              | some shiftedLocal =>
                  -- `GregorianCalendar.add(MONTH, …)` resolves the constructed
                  -- target as a fresh label. At the repeated 1916 midnight both
                  -- signed directions therefore choose the later CET instant,
                  -- unlike forward `DAY_OF_MONTH` addition.
                  match checked.source.profile.resolveLocal? shiftedLocal with
                  | none =>
                      throw (.landingUnavailable checked.unit parts offset)
                  | some shiftedInstant =>
                      pure (.value shiftedInstant shifted notGiven)
      | .years =>
          match LocalDateTime.ofYmdHms?
              parts.year parts.month parts.day 0 0 0 with
          | none => throw (.landingUnavailable checked.unit parts offset)
          | some sourceLocal =>
              match checked.source.profile.resolveLocal? sourceLocal with
              | none => throw (.landingUnavailable checked.unit parts offset)
              | some sourceInstant =>
                  match EuropeBerlinLegacyProfile.calendarYearLanding?
                      sourceLocal sourceInstant offset with
                  | none =>
                      throw (.landingUnavailable checked.unit parts offset)
                  | some (shifted, shiftedInstant) =>
                      pure (.value shiftedInstant
                        shifted.date.civil.parts notGiven)

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

end CheckedConstructedDateShift

/-- Structural failure outside the reason-bearing result of a checked constructed-Date difference. -/
inductive ConstructedDateDifferenceFault where
  | source (error : ConstructedDateEvaluationFault)
  | operationUnavailable
      (unit : DateShiftUnit)
      (first second : DateConstructionResult)
  deriving Repr, DecidableEq

/-- Two checked constructed-Date sources and one supplied day/month/year difference unit. -/
structure CheckedConstructedDateDifference (model : FlatModel) where
  first : CheckedConstructedDateComponents model
  second : CheckedConstructedDateComponents model
  unit : DateShiftUnit
  profileIsUtc :
    ModelZone.ConcreteProfile.ofId? model.timeZoneId = some .utc

namespace CheckedConstructedDateDifference

/-- Delegate one resolved pair to the established default-cutover day or completed-period owner. -/
def differenceResolved? (unit : DateShiftUnit)
    (first second : DateConstructionResult) :
    Option ConstructedDateNumericResult :=
  match unit with
  | .days => first.differenceLegacyDays? second
  | .months => first.differenceLegacy? .months second
  | .years => first.differenceLegacy? .years second

/-- Evaluate the first constructed Date before the second with one explicit optional world, preserve the first reached formal cause, and reuse the established reason-bearing numeric result. -/
def evaluate (checked : CheckedConstructedDateDifference model)
    (phase : Phase) (input : CheckedDocument model)
    (world : Option World) :
    Except ConstructedDateDifferenceFault
      (Except FormalCause ConstructedDateNumericResult) :=
  match checked.first.evaluate phase input world with
  | .error error => .error (.source error)
  | .ok (.unavailable cause) => .ok (.error cause)
  | .ok (.resolved first) =>
      match checked.second.evaluate phase input world with
      | .error error => .error (.source error)
      | .ok (.unavailable cause) => .ok (.error cause)
      | .ok (.resolved second) =>
          match differenceResolved? checked.unit first second with
          | some result => .ok (.ok result)
          | none =>
              .error (.operationUnavailable checked.unit first second)

end CheckedConstructedDateDifference

end A12Kernel
