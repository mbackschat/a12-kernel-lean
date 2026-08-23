import A12Kernel.Elaboration.TemporalTargetPolicy
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

The operand is a **bare** path: bracketing it is a parse failure, as it is for `ValueAsDate`. A repeatable
source is outside this capsule, whose gate requires a nonrepeatable declaration. -/

namespace A12Kernel

/-- Whether one resolved declaration is a nonrepeatable **complete** DateTime source, which is what both
DateTime component extractors require. -/
def FlatModel.admitsCompleteDateTimeSource
    (model : FlatModel) (source : FlatTemporalField) : Bool :=
  match model.lookupUniqueId source.id with
  | .error _ => false
  | .ok declaration =>
      declaration.repeatableScope.isEmpty &&
        declaration.toTemporalField? == some source &&
        source.kind == .dateTime &&
        source.components.isFullDateTime

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

end A12Kernel
