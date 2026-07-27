import A12Kernel.Elaboration.ConstructedDateComponents
import A12Kernel.Semantics.ConstructedDateDay

/-! # Checked constructed-Date execution

This capsule reads one certified direct three-Number-field Date from the immutable checked document in Day/Month/Year order. It wraps the existing cause-free construction result only to retain the first reached formal cause, then delegates calendar reality and literal day/month/year shifts to the default-cutover owners.

Expression-valued amounts, another component form or model zone, DateTime, repeatable placement, targets, and a general temporal-expression tree remain outside.
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

end A12Kernel
