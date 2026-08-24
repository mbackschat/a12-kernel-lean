import A12Kernel.Elaboration.TemporalTargetPolicy
import A12Kernel.Elaboration.FullDateComputationApplication
import A12Kernel.Semantics.DateFromDateTime

/-! # Checked `DateFromDateTime`

Static admission for the Date-valued DateTime component extractor. What it evaluates to belongs to
[`Semantics/DateFromDateTime.lean`](../Semantics/DateFromDateTime.lean); what a *legal* model may write
is here.

**One source gate serves both component extractors.** Measured at kernel 30.8.1, the Kernel wants a
complete DateTime for `DateFromDateTime` exactly as it does for `TimeFromDateTime`, and refuses anything
else at the operator itself: a DateTime declared with the degenerate time-only format and a plain Date
field are both `MVK_WRONG_DATE_FORMAT_FOR_OP`. So the predicate below is the shared owner and
`TimeFromDateTime`'s existing gate delegates to it rather than restating it.

**The result is a Date, and that is measured rather than assumed.** It compares against a Date field, a
Date literal position, `Today`, and another extraction, and it is admitted as a Date-addition operand;
comparing it to `Now` or to a `TimeFromDateTime` result is refused `MVK_INVALID_COMPARE_TO_DATE`. That
pair of refusals is what establishes the result's kind, because an admission alone would not distinguish
a Date result from a DateTime one that merely compares well.

The operand is a **bare** path: bracketing it is a parse failure, as it is for `ValueAsDate`. The scalar carrier below requires a nonrepeatable source; bounded repeatable execution belongs to [`AddressedDateFromDateTime.lean`](AddressedDateFromDateTime.lean). -/

namespace A12Kernel

/-- Whether one resolved declaration is a **complete** DateTime source whose repetition is bound by the reading scope. -/
def FlatModel.admitsCompleteDateTimeSourceIn
    (model : FlatModel) (scope : List RepeatableLevel)
    (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repetitionBoundBy scope &&
        declaration.toTemporalField? == some source &&
        source.kind == .dateTime &&
        source.components.isFullDateTime

/-- The scalar instance shared by both nonrepeatable DateTime component extractors. -/
def FlatModel.admitsCompleteDateTimeSource
    (model : FlatModel) (source : FlatTemporalField) : Bool :=
  model.admitsCompleteDateTimeSourceIn [] source

/-- Static refusal before a `DateFromDateTime` read is admitted. The Kernel reports one class,
`MVK_WRONG_DATE_FORMAT_FOR_OP`, for every source shape below; the arms are split finer here so a
consumer can say *which* requirement failed while still mapping them all to that one code. -/
inductive DateFromDateTimeElabError where
  | source (error : ResolveError)
  | sourceNotTemporal (field : FieldId)
  | sourceKind (field : FieldId) (actual : TemporalKind)
  /-- A DateTime whose component set is incomplete, which is the degenerate time-only declaration. -/
  | sourceComponents (field : FieldId) (actual : TemporalComponents)
  | unsupportedZone (zoneId : String)
  deriving Repr, DecidableEq

/-- One checked `DateFromDateTime` read: a complete-DateTime source and the model zone its extracted
Date's own midnight is resolved in. -/
structure CheckedDateFromDateTime (model : FlatModel) where
  private mk ::
  source : FlatTemporalField
  profile : ModelZone.ConcreteProfile
  sourceAdmitted : model.admitsCompleteDateTimeSource source = true
  profileOwned : ModelZone.ConcreteProfile.ofId? model.timeZoneId = some profile

/-- Resolve and certify one nonrepeatable `DateFromDateTime` read. -/
def elaborateDateFromDateTime (model : FlatModel) (sourceField : FieldId) :
    Except DateFromDateTimeElabError (CheckedDateFromDateTime model) := do
  let declaration ← (model.lookupUniqueId sourceField).mapError .source
  match declaration.toTemporalField? with
  | none => throw (.sourceNotTemporal sourceField)
  | some source =>
      if source.kind != .dateTime then
        throw (.sourceKind sourceField source.kind)
      else if !source.components.isFullDateTime then
        throw (.sourceComponents sourceField source.components)
      else
        if hSource : model.admitsCompleteDateTimeSource source then
          match hProfile :
              ModelZone.ConcreteProfile.ofId? model.timeZoneId with
          | none => throw (.unsupportedZone model.timeZoneId)
          | some profile =>
              pure { source, profile
                     sourceAdmitted := hSource, profileOwned := hProfile }
        else
          throw (.source (.repeatableReference declaration.path))

namespace CheckedDateFromDateTime

/-- Extract the Date at one already phase-classified source value. `none` identifies a payload whose
runtime kind contradicts the checked declaration, or a forged label with no resolvable midnight. -/
def extract? (checked : CheckedDateFromDateTime model)
    (value : TemporalValue) : Option DateValue :=
  dateFromDateTime? checked.profile value

end CheckedDateFromDateTime

/-! ## Checked computation carrier -/

/-- Static refusal before one bounded `DateFromDateTime` computation can execute. The source and target
certificates retain their existing finer diagnostics rather than introducing another mapping. -/
inductive DateFromDateTimeComputationElabError where
  | source (error : DateFromDateTimeElabError)
  | target (error : FullDateTargetElabError)
  deriving Repr, DecidableEq

/-- One checked extraction paired with the existing declaration-owned full-Date target. -/
structure CheckedDateFromDateTimeComputation (model : FlatModel) where
  source : CheckedDateFromDateTime model
  target : CheckedFullDateTarget model

/-- Resolve one nonrepeatable complete-DateTime source and one full-Date target in the same model. -/
def elaborateDateFromDateTimeComputation
    (model : FlatModel) (sourceField targetField : FieldId) :
    Except DateFromDateTimeComputationElabError
      (CheckedDateFromDateTimeComputation model) := do
  let source ← elaborateDateFromDateTime model sourceField |>.mapError .source
  let target ← elaborateFullDateTarget model targetField |>.mapError .target
  pure { source, target }

/-- Structural failure outside the rich full-Date target result domain. -/
inductive DateFromDateTimeComputationFault where
  | document (error : CheckedDocumentError)
  | sourceValueKind (source : FieldId)
  | sourceExtractionUnavailable (source : FieldId)
  | target (error : FullDateTargetEvaluationFault)
  deriving Repr, DecidableEq

namespace CheckedDateFromDateTimeComputation

/-- Read the source once at computation phase, preserving clean absence and formal poison before
projecting a present DateTime label to its model-zone Date midnight. -/
def evaluateOperand (operation : CheckedDateFromDateTimeComputation model)
    (input : CheckedDocument model) :
    Except DateFromDateTimeComputationFault TemporalComputationResult :=
  match input.read { field := operation.source.source.id, path := [] } with
  | .error error => .error (.document error)
  | .ok cell =>
      match observeCell .computation cell with
      | .empty => pure .noValue
      | .poison cause | .unknown cause => pure (.poison cause)
      | .value (.temporal value) =>
          match operation.source.extract? value with
          | some date => pure (.value date.instant)
          | none => throw (.sourceExtractionUnavailable operation.source.source.id)
      | .value _ => throw (.sourceValueKind operation.source.source.id)

/-- Execute the extracted Date through the existing declaration-owned target policy. -/
def evaluateOutcome (operation : CheckedDateFromDateTimeComputation model)
    (input : CheckedDocument model) :
    Except DateFromDateTimeComputationFault FullDateTargetOutcome :=
  match operation.evaluateOperand input with
  | .error error => .error error
  | .ok result => operation.target.evaluate result |>.mapError .target

/-- Project the checked target outcome into the ordinary full-Date computation result collections. -/
def executeResult (operation : CheckedDateFromDateTimeComputation model)
    (input : CheckedDocument model) (residualMessages : List ResidualMessage) :
    Except DateFromDateTimeComputationFault
      (FullDateComputationRunView ResidualMessage) := do
  let outcome ← operation.evaluateOutcome input
  pure (FullDateComputationRunView.fromOutcomes input residualMessages
    [(operation.target.checked.target.id, outcome)])

end CheckedDateFromDateTimeComputation

end A12Kernel
