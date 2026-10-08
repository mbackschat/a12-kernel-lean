import A12Kernel.Elaboration.HavingEntityList
import A12Kernel.Semantics.HavingTemporalSelection
import A12Kernel.Elaboration.PartialDateInput

namespace A12Kernel.HavingTemporalSelection

private def partialFormat (declaration : FlatFieldDecl) : Option FullDateTargetFormat := do
  let policy ← declaration.toTemporalTargetPolicy?
  if policy.partialMode == .full then none else FullDateTargetFormat.ofSource? policy.format

/-- First-filled requires exact declared formats; extrema compare supplemented component sets
(spec/07 §5; spec/04 extrema). Partial precision remains a FirstFilledValue-only source. -/
def profilesAgree (selection : HavingTemporalSelection) (model : FlatModel)
    (slots : List (HavingFieldListSlot HavingTemporalSelectionRef)) : Bool :=
  let references := slots.flatMap (·.references)
  match references.head? with
  | none => false
  | some first => references.all fun reference =>
      (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
        declaration.toTemporalField? == some reference.field &&
          reference.partialFormat == partialFormat declaration &&
          (if declaration.toTemporalTargetPolicy?.any (·.partialMode != .full) then
            selection == .firstFilled && (certifyPartialDateInputField declaration).isOk else true) &&
          match selection with
          | .extremum _ => reference.field.components.withBaseYear model.hasBaseYear ==
              first.field.components.withBaseYear model.hasBaseYear
          | .firstFilled => reference.field.components == first.field.components &&
              (declaration.toTemporalTargetPolicy?.map (·.format)) ==
                ((model.lookupUniqueId first.field.id).toOption.bind (·.toTemporalTargetPolicy?) |>.map (·.format))

def wellFormed (selection : HavingTemporalSelection) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel)
    (slots : List (HavingFieldListSlot HavingTemporalSelectionRef)) : Bool :=
  havingEntityListWellFormed model candidateLevels outerLevels (presenceSlots slots) &&
    selection.profilesAgree model slots

def elaborate (selection : HavingTemporalSelection) (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingEntitySource) :
    Except CorrelationElabError (List (HavingFieldListSlot HavingTemporalSelectionRef)) := do
  let operands ← elaborateHavingEntityList model declaringGroup candidateLevels outerLevels source
  let slots ← operands.mapM fun slot => slot.mapM fun reference => do
    let some field := reference.declaration.toTemporalField? | throw .numericExpressionUnsupported
    pure ({ origin := reference.origin, field, partialFormat := partialFormat reference.declaration } : HavingTemporalSelectionRef)
  if !selection.profilesAgree model slots then throw .numericExpressionUnsupported
  pure slots

end A12Kernel.HavingTemporalSelection
