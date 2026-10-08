import A12Kernel.Elaboration.HavingEntityList

namespace A12Kernel.HavingNumberAggregate

def wellFormed (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (slots : List (HavingFieldListSlot HavingNumberRef)) : Bool :=
  havingEntityListWellFormed model candidateLevels outerLevels (presenceSlots slots) &&
    (slots.flatMap (·.references)).all fun reference =>
      (model.lookupUniqueId reference.field.id).toOption.any fun declaration =>
        declaration.toNumberField? == some reference.field

def certify (slots : List (HavingFieldListSlot (ResolvedHavingDirectFieldOperand model))) :
    Except CorrelationElabError (List (HavingFieldListSlot HavingNumberRef)) := do
  slots.mapM fun slot => slot.mapM fun reference => do
    let some field := reference.declaration.toNumberField? | throw .numericExpressionUnsupported
    pure { origin := reference.origin, field }

/-- Numeric lists inherit ordinary shape gates before certifying every expanded declaration
as Number-valued; mixed signedness remains per declaration (spec/04 aggregates). -/
def elaborate (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingEntitySource) :
    Except CorrelationElabError (List (HavingFieldListSlot HavingNumberRef)) := do
  certify (← elaborateHavingEntityList model declaringGroup candidateLevels outerLevels source)

end A12Kernel.HavingNumberAggregate
