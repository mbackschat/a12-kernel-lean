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

private def availability : CheckedConstructedDateComponent →
    DateComponentAvailability
  | .value _ => .present
  | .empty => .empty
  | .unavailable _ => .unknown

private def resolve
    (day month year : CheckedConstructedDateComponent) :
    ConstructedDateObservation :=
  let reality := match day, month, year with
    | .value day, .value month, .value year =>
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

/-- Read Day, Month, and Year in generated argument order. A reached formal component stops before later reads and retains its exact cause. -/
def evaluate (checked : CheckedConstructedDateComponents model)
    (phase : Phase) (input : CheckedDocument model) :
    Except ConstructedDateEvaluationFault ConstructedDateObservation := do
  let day ← checked.day.read phase input
  match day with
  | .unavailable cause => pure (.unavailable cause)
  | day =>
      let month ← checked.month.read phase input
      match month with
      | .unavailable cause => pure (.unavailable cause)
      | month =>
          let year ← checked.year.read phase input
          match year with
          | .unavailable cause => pure (.unavailable cause)
          | year => pure (resolve day month year)

end CheckedConstructedDateComponents

end A12Kernel
