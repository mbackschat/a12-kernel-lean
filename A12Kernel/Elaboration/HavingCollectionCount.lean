import A12Kernel.Elaboration.ValueCountAdmission
import A12Kernel.Elaboration.HavingNumberAggregate

namespace A12Kernel

def HavingCollectionCount.capacity? (model : FlatModel)
    (slots : List (HavingFieldListSlot HavingPresenceRef)) : Option Nat :=
  slots.foldlM (m := Option) (init := 0) fun total slot => do
    let capacity ← match slot with
      | .direct _ => some 1
      | .extent (.group source) _ => model.groupSubtreeSlotCapacity? source.path
      | .extent source references => do
          let declarations ← references.mapM fun ref => (model.lookupUniqueId ref.field).toOption
          model.declarationsSlotCapacity? source.boundCount declarations
    pure (total + capacity)

private def tokenSlotsMatch (model : FlatModel) (slots : List (HavingFieldListSlot HavingStringRef))
    (expected : Option String) : Bool :=
  slots.all fun slot => slot.references.all fun ref =>
    (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
      let projectionAllowed := (match slot with
        | .direct _ | .extent (.starField _ _) _ => expected.isSome
        | _ => false) || declaration.toTextFieldComparison?.any (fun (operand, _) => operand == ref.operand)
      projectionAllowed &&
      (match ref.operand with
        | .string _ => declaration.toTextFieldComparison?.any (fun (operand, _) => operand == ref.operand)
        | .enumeration operand => declaration.toEnumerationTextFieldComparison? operand.projectionRef
            |>.any (fun (resolved, _) => resolved == ref.operand)) &&
        expected.all (declaration.allowsTokenValueCountLiteral ref.operand)

def HavingCollectionCount.wellFormed (source : HavingCollectionCount) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  (match source with
    | .tokenValue _ slots => havingTypedEntityListWellFormed model candidateLevels outerLevels
        (fun (ref : HavingStringRef) => ({ origin := ref.origin, field := ref.field.id } : HavingPresenceRef)) slots
    | _ => havingEntityListWellFormed model candidateLevels outerLevels source.presenceSlots) &&
    match source with
    | .filledFields slots capacity => HavingCollectionCount.capacity? model slots == capacity
    | .numberValue _ slots => HavingNumberAggregate.wellFormed model candidateLevels outerLevels slots
    | .tokenValue expected slots => tokenSlotsMatch model slots (some expected)
    | .tokenDistinct slots => tokenSlotsMatch model slots none
    | .temporalDistinct baseYear components slots =>
        baseYear == model.baseYear && timeBearingSetIsComplete components &&
          (slots.flatMap (·.references)).head?.any (fun ref => ref.field.components == components) &&
          (slots.flatMap (·.references)).all (fun ref =>
            (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
              declaration.toTemporalField? == some ref.field &&
                declaration.toTemporalTargetPolicy?.any (·.partialMode == .full) &&
                ref.field.components.supplementedByBaseYear model.hasBaseYear ==
                  components.supplementedByBaseYear model.hasBaseYear)
    | .booleanValue expected slots => (slots.flatMap (·.references)).all fun ref =>
        (model.lookupUniqueId ref.field).toOption.any fun declaration =>
          booleanValueCountKindAllowed expected declaration.policy.kind

private def tokenSlots (checked : List (HavingFieldListSlot (ResolvedHavingDirectFieldOperand model)))
    (expected : Option String) : Except CorrelationElabError (List (HavingFieldListSlot HavingStringRef)) := do
  let slots ← checked.mapM fun slot => slot.mapM fun ref => do
    let profile := match ref.form with
      | .stored => ref.declaration.toTextFieldComparison?
      | .projected category => ref.declaration.toEnumerationTextFieldComparison? (.category category)
    let some (operand, _) := profile | throw .numericExpressionUnsupported
    pure ({ origin := ref.origin, operand } : HavingStringRef)
  if !((checked.flatMap (·.references)).zip (slots.flatMap (·.references))).all
      (fun (resolved, ref) => expected.all (resolved.declaration.allowsTokenValueCountLiteral ref.operand)) then
    throw .numericExpressionUnsupported
  pure slots


def elaborateHavingCollectionCount (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) :
    SurfaceHavingCollectionCount → Except CorrelationElabError HavingCollectionCount
  | .numberValue expected source =>
      .numberValue expected <$> HavingNumberAggregate.elaborate model declaringGroup candidateLevels outerLevels source
  | .tokenValue expected source => do
      let checked ← resolveHavingProjectedEntityList model declaringGroup candidateLevels outerLevels source
      pure (.tokenValue expected (← tokenSlots checked (some expected)))
  | .booleanValue expected source => do
      let checked ← elaborateHavingEntityList model declaringGroup candidateLevels outerLevels source
      let slots ← checked.mapM fun slot => slot.mapM fun ref => do
        if !booleanValueCountKindAllowed expected ref.declaration.policy.kind then throw .numericExpressionUnsupported
        pure ({ origin := ref.origin, field := ref.declaration.id } : HavingPresenceRef)
      pure (.booleanValue expected slots)
  | .filledFields source => do
      let checked ← elaborateHavingEntityList model declaringGroup candidateLevels outerLevels source
      let slots := checked.map (·.map fun ref => ({ origin := ref.origin, field := ref.declaration.id } : HavingPresenceRef))
      pure (.filledFields slots (HavingCollectionCount.capacity? model slots))

def elaborateHavingDistinctCount (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingEntitySource) :
    Except CorrelationElabError (HavingNumericAtomOf Empty) := do
  let checked ← elaborateHavingEntityList model declaringGroup candidateLevels outerLevels source
  let some first := (checked.flatMap (·.references)).head? | throw .numericExpressionUnsupported
  match first.declaration.policy.kind with
  | .number _ => .aggregate .distinctCount <$> HavingNumberAggregate.certify checked
  | .string | .enumeration => return .collectionCount (.tokenDistinct (← tokenSlots checked none))
  | .temporal _ components => do
      if !timeBearingSetIsComplete components then throw .numericExpressionUnsupported
      let slots ← checked.mapM fun slot => slot.mapM fun ref => do
        let some field := ref.declaration.toTemporalField? | throw .numericExpressionUnsupported
        if !ref.declaration.toTemporalTargetPolicy?.any (·.partialMode == .full) then throw .numericExpressionUnsupported
        if field.components.supplementedByBaseYear model.hasBaseYear !=
            components.supplementedByBaseYear model.hasBaseYear then throw .numericExpressionUnsupported
        pure ({ origin := ref.origin, field } : HavingTemporalRef)
      pure (.collectionCount (.temporalDistinct model.baseYear components slots))
  | _ => throw .numericExpressionUnsupported

end A12Kernel
