import A12Kernel.Elaboration.FullDateComputationApplication
import A12Kernel.Elaboration.ValueAsDate

/-! # Partial-Date shift into a checked Date target

This capsule composes one checked `ValueAsDate` calendar shift with the existing nonrepeatable full-Date target, five-collection result view, and application boundary. The shift keeps a real civil landing until the target renders and checks it, so an always-on floor failure retains the attempted text as an errored computed instance. The bounded route fails closed before the legacy `GregorianCalendar` cutover: a proleptic civil landing there no longer identifies the Kernel's observable attempted label. Wider hybrid-calendar execution, scheduling, repeatable targets, and message text remain separate.
-/

namespace A12Kernel

/-- Static refusal before a partial-Date shift and its distinct Date target can be paired. -/
inductive ValueAsDateShiftTargetElabError where
  | shift (error : ValueAsDateElabError)
  | target (error : FullDateTargetElabError)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- One checked partial-Date shift and one distinct target from the same validated model. -/
structure CheckedValueAsDateShiftTarget (model : FlatModel) where
  shift : CheckedValueAsDateShift model
  target : CheckedFullDateTarget model
  targetsDistinct : shift.source.target.id ≠ target.checked.target.id

/-- Structural failure outside the rich target-outcome domain. -/
inductive ValueAsDateShiftTargetFault where
  | shift (error : ValueAsDateShiftFault)
  | unsupportedLegacyLanding (date : CivilDate)
  deriving Repr, DecidableEq

namespace CheckedValueAsDateShiftTarget

/-- First civil label on the Gregorian side of the default legacy-calendar cutover. UTC, GMT, and the pinned Berlin profile agree with the proleptic account from this label onward. -/
private def firstSupportedLanding : CivilDate := {
  parts := { year := 1582, month := 10, day := 15 }
  real := by decide
}

/-- Consume one already checked source cell and numeric amount, retaining semantic no-value and poison while routing every supported real landing through the existing target policy. -/
def evaluateOutcome (checked : CheckedValueAsDateShiftTarget model)
    (cell : CheckedCell
      (AdmittedPartiallyKnownDate checked.shift.source.policy.partialMode))
    (amount : NumericComputationResult) :
    Except ValueAsDateShiftTargetFault FullDateTargetOutcome := do
  let result ← checked.shift.evaluate cell amount |>.mapError .shift
  match result with
  | .noValue | .nonRelevant => pure .noValue
  | .poison cause => pure (.poison cause)
  | .value date =>
      if date.Before firstSupportedLanding then
        throw (.unsupportedLegacyLanding date)
      else
        pure (checked.target.evaluateCivil date)

/-- Check the bounded raw partial-Date source before executing the checked shift and target. -/
def evaluateRaw (checked : CheckedValueAsDateShiftTarget model)
    (raw : RawCell String) (amount : NumericComputationResult) :
    Except ValueAsDateShiftTargetFault FullDateTargetOutcome :=
  checked.evaluateOutcome
    (checked.shift.toCheckedValueAsDateSource.checkSourceRaw raw) amount

/-- Execute one raw partial-Date shift and classify its rich target outcome against the immutable source placement of the target. The checked document is not a second partial-Date parser. -/
def executeResult (checked : CheckedValueAsDateShiftTarget model)
    (input : CheckedDocument model)
    (raw : RawCell String) (amount : NumericComputationResult)
    (residualMessages : List ResidualMessage) :
    Except ValueAsDateShiftTargetFault
      (FullDateComputationRunView ResidualMessage) := do
  let outcome ← checked.evaluateRaw raw amount
  pure (FullDateComputationRunView.fromOutcomes input residualMessages
    [(checked.target.checked.target.id, outcome)])

end CheckedValueAsDateShiftTarget

/-- Resolve one checked special-Date shift and one distinct nonrepeatable Date target. -/
def elaborateValueAsDateShiftTarget
    (model : FlatModel) (sourceField targetField : FieldId)
    (endpoint : ValueAsDateEndpoint) (unit : ValueAsDateShiftUnit) :
    Except ValueAsDateShiftTargetElabError
      (CheckedValueAsDateShiftTarget model) := do
  let shift ←
    elaborateValueAsDateShift model sourceField endpoint unit |>.mapError .shift
  let target ← elaborateFullDateTarget model targetField |>.mapError .target
  if sameTarget : shift.source.target.id = target.checked.target.id then
    throw (.targetSelfReference targetField)
  else
    pure { shift, target, targetsDistinct := sameTarget }

end A12Kernel
