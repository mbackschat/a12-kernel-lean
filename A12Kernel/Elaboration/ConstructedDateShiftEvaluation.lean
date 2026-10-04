import A12Kernel.Elaboration.ConstructedDateEvaluation
import A12Kernel.Elaboration.TemporalShiftAmount
import A12Kernel.Semantics.BerlinLegacyCalendarArithmetic

/-! # Checked constructed-Date shifts

This capsule evaluates one checked constructed Date followed by one or two generated
calendar shifts. Fresh Date construction resolves a wall label exactly once. A nested
shift consumes the inner result's exact instant directly, and a Date comparison
projects that same retained instant into the shared temporal comparison domain, so
repeated-hour identity is never lost through label reconstruction.

UTC/GMT retain the carried legacy-hybrid date identity. Pinned Berlin decodes each
continuation source from its exact instant before applying the unit-specific field
mutation. A general temporal-expression tree, DateTime operands, target storage, other
model zones, and shift-to-difference composition remain outside.
-/

namespace A12Kernel

/-- Compatibility name for the shared exact constructed-Date value boundary. -/
abbrev ConstructedDateShiftResult := ConstructedDateValue

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

/-- Calendar mutation consumes the carried instant without re-resolving its label; target
storage restrictions belong to the later consumer (spec/05 and calendar-expression grid). -/
private def applyResolvedRealAmount
    (checked : CheckedConstructedDateShift model)
    (sourceInstant : Instant) (parts : DateParts)
    (offset : Int) (notGiven : Bool) :
    Except ConstructedDateShiftFault ConstructedDateShiftResult :=
  match checked.source.profile.shiftCalendar? checked.unit sourceInstant offset with
  | some (label, instant) => pure (.value instant label.parts notGiven)
  | none => throw (.landingUnavailable checked.unit parts offset)

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
  match checked.source.evaluateValue phase input world with
  | .error error => .error (.source error)
  | .ok (.unavailable cause) => .ok (.unavailable cause)
  | .ok source =>
      match checked.amount.read phase input with
      | .error error => .error (.amountDocument error)
      | .ok (.error (.formal cause)) => .ok (.unavailable cause)
      | .ok (.error unavailable) => .error (.amountUnavailable unavailable)
      | .ok (.ok outcome) => checked.applyResultAmount source outcome

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
