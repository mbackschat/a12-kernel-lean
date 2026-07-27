import A12Kernel.Elaboration.ConstructedDateComponents
import A12Kernel.Elaboration.TemporalShiftAmount
import A12Kernel.Semantics.ConstructedDateDay

/-! # Checked constructed-Date execution

This capsule evaluates one certified direct constructed Date in generated component order. Number fields and direct Date/DateTime extractors read the immutable checked document, while fixed components do not; the two-argument form uses the model Base Year, and the four-argument form reads Century before Short-Year and combines them only when both are present. It wraps the existing cause-free construction result only to retain the first reached formal cause, then delegates calendar reality and literal day/month/year shifts to the default-cutover owners.

The same checked source may be shifted by a literal, ordinary Number field, or checked same-group numeric expression. Source components are evaluated before the amount; exact formal causes, missing provenance, arithmetic domain failure, and Java signed-32-bit narrowing remain distinguishable. String components, recursive extractor operands, another model zone, repeatable placement, targets, and a general temporal-expression tree remain outside.
-/

namespace A12Kernel

/-- Structural failure outside Date-construction reason semantics. -/
inductive ConstructedDateEvaluationFault where
  | document (error : CheckedDocumentError)
  | payloadKind (field : FieldId)
  | nonIntegralPayload (field : FieldId) (value : Rat)
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

namespace CheckedConstructedDateSource

/-- Read a field-backed component or return an authored constant without consulting the document. -/
def read (checked : CheckedConstructedDateSource model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match checked with
  | .numberField source => source.read phase input
  | .constant value => pure (.value value)
  | .extractor source => source.read phase input

end CheckedConstructedDateSource

namespace CheckedConstructedDateYear

/-- Read one checked year form. Split-year evaluation preserves Century-before-Short-Year formal precedence, while any ordinary empty component keeps the construction incomplete. -/
def read (checked : CheckedConstructedDateYear model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault CheckedConstructedDateComponent :=
  match checked with
  | .complete source => source.read phase input
  | .baseYear year => pure (.value year)
  | .centuryAndShortYear century shortYear =>
      match century.read phase input with
      | .error error => .error error
      | .ok (.unavailable cause) => .ok (.unavailable cause)
      | .ok centuryPart =>
          match shortYear.read phase input with
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

private def availableAmount? : CheckedConstructedDateComponent → Option Int
  | .value amount => some amount
  | .empty | .unavailable _ => none

/-- Read Day, Month, and Year in generated argument order. A reached formal component stops before later reads and retains its exact cause. -/
def evaluate (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault ConstructedDateObservation :=
  match checked.day.read phase input with
  | .error error => .error error
  | .ok (.unavailable cause) => .ok (.unavailable cause)
  | .ok day =>
      match checked.month.read phase input with
      | .error error => .error error
      | .ok (.unavailable cause) => .ok (.unavailable cause)
      | .ok month =>
          match checked.year.read phase input with
          | .error error => .error error
          | .ok (.unavailable cause) => .ok (.unavailable cause)
          | .ok year =>
              .ok (ConstructedDateObservation.ofAvailableComponents
                (availableAmount? day) (availableAmount? month)
                (availableAmount? year))

/-- Evaluate checked `Valid(Date(...))`, keeping document faults and formal causes in their separate channels. -/
def evaluateValid (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault (Except FormalCause Verdict) :=
  (checked.evaluate phase input).map ConstructedDateObservation.validVerdict

/-- Evaluate checked `Invalid(Date(...))`, keeping document faults and formal causes in their separate channels. -/
def evaluateInvalid (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault (Except FormalCause Verdict) :=
  (checked.evaluate phase input).map ConstructedDateObservation.invalidVerdict

/-- Evaluate one checked Day/Month/Quarter/Year projection without adding another numeric result family. -/
def evaluateNumericPart (checked : CheckedConstructedDateComponents model)
    (part : DateNumericPart) (phase : Phase)
    (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault
      (Except FormalCause ConstructedDateNumericResult) :=
  (checked.evaluate phase input).map fun observation =>
    observation.numericPart part

end CheckedConstructedDateComponents

/-- Reason-bearing result of one checked constructed-Date calendar shift. -/
inductive ConstructedDateShiftResult where
  | noValue (notGiven : Bool)
  | value (parts : DateParts) (notGiven : Bool)
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

/-- One checked constructed-Date source, calendar unit, and direct-Number shift amount. -/
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
          match shiftResolved? checked.unit (.real parts) offset with
          | some (.real shifted) => pure (.value shifted notGiven)
          | some .incomplete => pure (.noValue notGiven)
          | some .unreal => pure (.noValue notGiven)
          | some .unknown => pure (.noValue notGiven)
          | none =>
              throw (.landingUnavailable checked.unit parts offset)
      | .resolved .incomplete => pure (.noValue notGiven)
      | .resolved .unreal => pure (.noValue notGiven)
      | .resolved .unknown => pure (.noValue notGiven)

/-- Evaluate the constructed Date before its amount, matching generated Java argument order. A reached source cause therefore stops before the amount; a cause-free no-value source still reaches it. -/
def evaluate (checked : CheckedConstructedDateShift model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateShiftFault ConstructedDateShiftResult :=
  match checked.source.evaluate phase input with
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

namespace CheckedConstructedDateDifference

/-- Delegate one resolved pair to the established default-cutover day or completed-period owner. -/
def differenceResolved? (unit : DateShiftUnit)
    (first second : DateConstructionResult) :
    Option ConstructedDateNumericResult :=
  match unit with
  | .days => first.differenceLegacyDays? second
  | .months => first.differenceLegacy? .months second
  | .years => first.differenceLegacy? .years second

/-- Evaluate the first constructed Date before the second, preserve the first reached formal cause, and reuse the established reason-bearing numeric result. -/
def evaluate (checked : CheckedConstructedDateDifference model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateDifferenceFault
      (Except FormalCause ConstructedDateNumericResult) :=
  match checked.first.evaluate phase input with
  | .error error => .error (.source error)
  | .ok (.unavailable cause) => .ok (.error cause)
  | .ok (.resolved first) =>
      match checked.second.evaluate phase input with
      | .error error => .error (.source error)
      | .ok (.unavailable cause) => .ok (.error cause)
      | .ok (.resolved second) =>
          match differenceResolved? checked.unit first second with
          | some result => .ok (.ok result)
          | none =>
              .error (.operationUnavailable checked.unit first second)

end CheckedConstructedDateDifference

end A12Kernel
