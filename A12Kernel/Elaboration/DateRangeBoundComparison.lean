import A12Kernel.Elaboration.YearlessDateRangeBound
import A12Kernel.Semantics.DateComparison

/-! # Comparing two extracted DateRange endpoints

A comparison between two selected DateRange endpoints is admitted by the ordinary direct
temporal rule over the two declarations' component sets, not by requiring identical sets: a
month-only endpoint may be compared with a month-and-day one, while a yearless endpoint and a
year-bearing one are refused unless the model's Base Year supplies the missing year. This
capsule owns that pair across both bound owners, because either side may be exact or yearless
and only the admitted pairs are homogeneous.

At runtime each side keeps its own domain. Two exact endpoints compare as resolved dates. Two
yearless endpoints are first completed by their authored position — a month-only start to the
first day, a month-only finish to the greatest day that month can ever have — and then compared
as labels, so no year is manufactured. Comparing an endpoint with a fixed full Date keeps its
existing owner, and its refusal for a yearless source is still reported there as local
ingestion insufficiency rather than the Kernel's own comparison diagnostic.
-/

namespace A12Kernel

/-- One extracted endpoint usable as a comparison operand, from either bound owner. -/
inductive CheckedDateRangeBoundOperand (model : FlatModel) where
  | exact (bound : CheckedDateRangeBound model)
  | yearless (bound : CheckedYearlessDateRangeBound model)

namespace CheckedDateRangeBoundOperand

/-- The declared component set the endpoint exposes. It is the source declaration's own set in
both cases: a Base-Year-completed value still answers for the components it declared, and the
Base Year is supplied by the admission rule instead. -/
def components : CheckedDateRangeBoundOperand model → TemporalComponents
  | .exact bound => bound.format.components
  | .yearless bound => bound.format.components

/-- The authored endpoint position, which decides a yearless label's completion. -/
def bound : CheckedDateRangeBoundOperand model → DateRangeBound
  | .exact bound => bound.bound
  | .yearless bound => bound.bound

end CheckedDateRangeBoundOperand

/-- Static refusal while certifying one endpoint pair. -/
inductive DateRangeBoundPairElabError where
  | left (cause : YearlessDateRangeBoundElabError)
  | right (cause : YearlessDateRangeBoundElabError)
  | formatsNotComparable (left right : TemporalComponents)
  deriving Repr, DecidableEq

namespace DateRangeBoundPairElabError

/-- Only the format refusal has an established Kernel diagnostic; an operand refusal is local
ingestion insufficiency. -/
def diagnostic? : DateRangeBoundPairElabError → Option KernelStaticDiagnostic
  | .formatsNotComparable _ _ => some .invalidCompareToDate
  | .left _ | .right _ => none

end DateRangeBoundPairElabError

/-- Certify one endpoint operand, preferring the exact-valued owner and falling back to the
yearless one only where the exact owner reports an unsupported policy. Every other refusal
propagates as itself, so a genuine source failure is never replaced by the policy cause. -/
def elaborateDateRangeBoundOperand (model : FlatModel) (source : FieldId)
    (bound : DateRangeBound) :
    Except YearlessDateRangeBoundElabError
      (CheckedDateRangeBoundOperand model) :=
  match elaborateDateRangeBound model source bound with
  | .ok exact => pure (.exact exact)
  | .error (.unsupportedPolicy _ _ _) =>
      .yearless <$> elaborateYearlessDateRangeBound model source bound
  | .error cause => throw (.source cause)

/-- One certified pair of extracted endpoints retained in authored order. -/
structure CheckedDateRangeBoundPair (model : FlatModel) where
  private mk ::
  left : CheckedDateRangeBoundOperand model
  right : CheckedDateRangeBoundOperand model
  comparison : TemporalComparisonOp
  formatsAdmitted :
    comparison.admitsFormats model.baseYear.isSome left.components
      right.components = true

/-- Certify both endpoints and their comparability. The gate is the ordinary direct temporal
admission rule, so it reads year presence and date-versus-time class rather than requiring
identical component sets. -/
def elaborateDateRangeBoundPair (model : FlatModel)
    (leftSource : FieldId) (leftBound : DateRangeBound)
    (rightSource : FieldId) (rightBound : DateRangeBound)
    (comparison : TemporalComparisonOp) :
    Except DateRangeBoundPairElabError
      (CheckedDateRangeBoundPair model) := do
  let left ← elaborateDateRangeBoundOperand model leftSource leftBound
    |>.mapError .left
  let right ← elaborateDateRangeBoundOperand model rightSource rightBound
    |>.mapError .right
  if hFormats : comparison.admitsFormats model.baseYear.isSome left.components
      right.components = true then
    pure { left, right, comparison, formatsAdmitted := hFormats }
  else
    throw (.formatsNotComparable left.components right.components)

/-- Defensive failure while reading one endpoint of the pair. -/
inductive DateRangeBoundPairFault where
  | leftExact (cause : DateRangeBoundFault)
  | rightExact (cause : DateRangeBoundFault)
  | leftYearless (cause : YearlessDateRangeBoundFault)
  | rightYearless (cause : YearlessDateRangeBoundFault)
  | selectedDateUnavailable (source : FieldId) (value : DateValue)
  | mixedDomains
  deriving Repr, DecidableEq

/-- One-read result retaining both endpoint domains beside the verdict they produced. Only a
homogeneous pair is admitted statically, so the two present shapes are both-exact and
both-yearless; a mixed pair is a defensive fault rather than a comparison. -/
inductive DateRangeBoundPairResult where
  | exact (left right : CellObservation FullDate) (verdict : Verdict)
  | yearless (left right : CellObservation MonthDayValue) (verdict : Verdict)
  deriving Repr, DecidableEq

namespace CheckedDateRangeBoundPair

/-- Project one exact endpoint observation into the established full-Date comparison domain. -/
private def exactObservation (source : FieldId) :
    CellObservation DateValue →
    Except DateRangeBoundPairFault (CellObservation FullDate)
  | .empty => .ok .empty
  | .value value =>
      match value.toFullDate? with
      | some date => .ok (.value date)
      | none => throw (.selectedDateUnavailable source value)
  | .unknown cause => .ok (.unknown cause)
  | .poison cause => .ok (.poison cause)

/-- Complete one yearless endpoint observation by its authored position. -/
private def yearlessObservation (bound : DateRangeBound) :
    CellObservation YearlessDateRangeBoundValue → CellObservation MonthDayValue
  | .empty => .empty
  | .value value => .value (value.completed bound)
  | .unknown cause => .unknown cause
  | .poison cause => .poison cause

/-- Read both endpoints once and compare them in their own domain. -/
def evaluate (checked : CheckedDateRangeBoundPair model)
    (input : CheckedDocument model) :
    Except DateRangeBoundPairFault DateRangeBoundPairResult :=
  match checked.left, checked.right with
  | .exact left, .exact right => do
      let leftObserved ← (left.evaluate .validation input).mapError .leftExact
      let rightObserved ← (right.evaluate .validation input).mapError .rightExact
      let leftDate ← exactObservation left.source.id leftObserved
      let rightDate ← exactObservation right.source.id rightObserved
      pure (.exact leftDate rightDate
        (checked.comparison.evalObserved leftDate rightDate))
  | .yearless left, .yearless right => do
      let leftObserved ← (left.evaluate .validation input).mapError .leftYearless
      let rightObserved ←
        (right.evaluate .validation input).mapError .rightYearless
      let leftLabel := yearlessObservation left.bound leftObserved
      let rightLabel := yearlessObservation right.bound rightObserved
      pure (.yearless leftLabel rightLabel
        (evalSymmetricComparison checked.comparison.holdsMonthDay
          leftLabel.asValidationSimpleOperand
          rightLabel.asValidationSimpleOperand))
  | _, _ => throw .mixedDomains

end CheckedDateRangeBoundPair

end A12Kernel
