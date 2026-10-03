import A12Kernel.Elaboration.DateConstantTarget
import A12Kernel.Elaboration.NumericSource
import A12Kernel.Elaboration.AddressedRepeatableTarget

namespace A12Kernel

inductive DateLiteralComputationElabError where
  | target (cause : ResolveError)
  | placement (cause : AddressedRepeatableTargetElabError)
  | calendar
  | rendering (cause : DateConstantTargetElabError)
  | incoherentTarget
  deriving Repr, DecidableEq

/-- One date assignment retaining written year presence separately from its model-dependent civil
completion. The target renderer certifies the literal/format pair; the source uses the same calendar
classification as date arithmetic, including the common-year check for an omitted year. -/
structure CheckedDateLiteralComputation (model : FlatModel) where
  private mk ::
  declaringGroup : GroupPath
  target : FlatFieldDecl
  source : AuthoredDateLiteral
  constant : CivilDate
  dateTarget : CheckedDateConstantTarget model source.year.isSome
  sourceValid : source.valid = true
  completed : CivilDate.ofYmd? (source.parts model.baseYearOrDefault).year
    source.month source.day = some constant
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
    match hDate : CivilDate.ofYmd? (source.parts model.baseYearOrDefault).year source.month source.day with
    | none => throw .calendar
    | some constant =>
        if hTarget : dateTarget.field = target.id then
          pure {
            declaringGroup, target, source, constant, dateTarget
            sourceValid := hValid, completed := hDate, sameTarget := hTarget }
        else throw .incoherentTarget
  else throw .calendar

/-- Store the completed literal through the declaration's existing render-and-check operation. -/
def CheckedDateLiteralComputation.outcome (operation : CheckedDateLiteralComputation model) :
    FullDateTargetOutcome :=
  operation.dateTarget.evaluateCivil operation.constant

end A12Kernel
