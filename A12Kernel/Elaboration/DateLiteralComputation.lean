import A12Kernel.Elaboration.DateConstantTarget
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.AddressedRepeatableTarget

namespace A12Kernel

inductive DateLiteralComputationElabError where
  | target (cause : ResolveError)
  | placement (cause : AddressedRepeatableTargetElabError)
  /-- The literal is no date on the hybrid calendar that static admission uses. -/
  | calendar
  | rendering (cause : DateConstantTargetElabError)
  | incoherentTarget
  deriving Repr, DecidableEq

/-- One date assignment retaining written year presence separately from its model-dependent
completion. The target renderer certifies the literal/format pair; the source uses the same static
classification as date arithmetic, including the common-year check for an omitted year. What the
literal denotes is decided when it is reached, in the model zone (spec/05 §1), so a Julian leap day the
proleptic calendar lacks is admitted here. -/
structure CheckedDateLiteralComputation (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  target : FlatFieldDecl
  source : AuthoredDateLiteral
  dateTarget : CheckedDateConstantTarget model source.year.isSome
  sourceValid : source.valid = true
  sameTarget : dateTarget.field = target.id

/-- Classify source validity before completing its absent year, and retain the existing fixed/row
placement and declaration-owned format gates. Runtime target policy runs only after rendering. -/
def checkDateLiteralComputation (model : FlatModel) (declaringGroup : GroupPath)
    (targetField : FieldId) (source : AuthoredDateLiteral) :
    Except DateLiteralComputationElabError (CheckedDateLiteralComputation model) := do
  if !GroupPath.isValid declaringGroup then throw (.target (.invalidRuleGroup declaringGroup))
  let target ← (model.lookupUniqueId targetField).mapError .target
  if !target.repeatableScope.isEmpty then
    let _ ← (checkAddressedRepeatableTarget model declaringGroup targetField).mapError .placement
  if hValid : source.valid = true then
    let dateTarget ← (elaborateDateConstantTargetIn model target.repeatableScope targetField
      source.year.isSome).mapError .rendering
    if hTarget : dateTarget.field = target.id then
      pure {
        declaringGroup, target, source, dateTarget
        sourceValid := hValid, sameTarget := hTarget }
    else throw .incoherentTarget
  else throw .calendar

/-- Store the literal through the declaration's existing render-and-check operation, after the model
zone resolves it as a stored label (spec/05 §1). Under UTC a Julian leap day keeps its Julian instant,
so it renders as the proleptic day of that instant and the target's own floor check judges it. Under
Europe/Berlin it has no instant: there is no outcome, and the carrier raises the value failure the
DateTime constant carrier raises. -/
def CheckedDateLiteralComputation.outcome? (operation : CheckedDateLiteralComputation model) :
    Option FullDateTargetOutcome :=
  (operation.dateTarget.profile.resolveConstantDateParts?
    (operation.source.parts model.baseYearOrDefault)).map fun value =>
      operation.dateTarget.evaluateParts value.parts

end A12Kernel
