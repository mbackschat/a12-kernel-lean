import A12Kernel.Elaboration.ConstructedDateComponents
import A12Kernel.Semantics.BaseYearDateSource
import A12Kernel.Semantics.ConstructedDateDay

/-! # Checked constructed-Date component execution

This capsule evaluates one certified direct constructed Date in generated component order. Number fields, pattern-backed String fields, the complete-Year `yyyy` Date field, and direct Date/DateTime extractors read the immutable checked document; constants and direct/range-selected Base-Year extractors are fixed inputs; and `Today`/`Now` resolve only from the execution's explicit optional `World`. The two-argument form uses the model Base Year, and the four-argument form reads Century before Short-Year and combines them only when both are present. It wraps the existing cause-free construction result only to retain the first reached formal cause. UTC/GMT retain the established hybrid-calendar reality; pinned Berlin additionally requires a post-floor local-midnight label admitted by its selected profile.

Exact formal causes and missing provenance remain distinguishable. Checked shifts and differences have their own execution owners in `ConstructedDateShiftEvaluation` and `ConstructedDateDifferenceEvaluation`. Berlin's pre-floor hybrid identity, the extensible-enumeration String alternative, other recursive extractor operands, another model zone, repeatable placement, targets, and a general temporal-expression tree remain outside.
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

end A12Kernel
