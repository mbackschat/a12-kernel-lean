import A12Kernel.Elaboration.HavingFieldValueList
import A12Kernel.Elaboration.HavingEntityList

namespace A12Kernel

/-- The ordinary category and exact-format gates inspect the complete declaration expansion;
runtime keeps the authored slots for ordered extent acquisition (spec/07 §5). -/
def elaborateHavingUniqueness (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingEntitySource) :
    Except CorrelationElabError HavingUniqueness := do
  let checked ← elaborateHavingEntityList model declaringGroup candidateLevels outerLevels source
  let declarations := checked.flatMap (fun slot => slot.references.map (·.declaration))
  let some first := declarations.head? | throw .incoherentCore
  if let some refusal := firstExpandedKindRefusal? declarations then throw (.uniquenessKind refusal.path)
  let .category category := first.policy.kind.surfaceKind.fieldListAdmission | throw .incoherentCore
  if let some refusal := firstExpandedCategoryMismatch? category declarations then throw (.membershipBaseType refusal.path)
  match category with
  | .number => return .number (← checked.mapM fun slot => slot.mapM fun operand => do
      let some field := operand.declaration.toNumberField? | throw .incoherentCore
      pure { origin := operand.origin, field })
  | .string | .enumeration => return .token (← checked.mapM fun slot => slot.mapM fun operand => do
      let some (field, _) := operand.declaration.toTextFieldComparison? | throw .incoherentCore
      pure { origin := operand.origin, operand := field })
  | .temporal =>
      let some policy := first.toTemporalTargetPolicy? | throw .incoherentCore
      let operands ← checked.mapM fun slot => slot.mapM fun operand => do
        let some other := operand.declaration.toTemporalTargetPolicy? | throw .incoherentCore
        if other.format != policy.format then throw (.uniquenessFormat operand.declaration.path)
        let some field := operand.declaration.toTemporalField? | throw .incoherentCore
        pure ({ origin := operand.origin, field } : HavingTemporalRef)
      pure (.temporal operands)

def HavingUniqueness.wellFormedForEnvironments (source : HavingUniqueness) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  havingEntityListWellFormed model candidateLevels outerLevels source.presenceSlots &&
    match source with
    | .number slots => (slots.flatMap (·.references)).all fun ref => (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
        (FlatField.number ref.field).matchesDecl declaration
    | .token slots =>
      let operands := slots.flatMap (·.references)
      operands.all fun ref => (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
        declaration.toTextFieldComparison?.any (fun (operand, _) => operand == ref.operand) &&
          operands.head?.any (fun first => match first.operand, ref.operand with
            | .string _, .string _ | .enumeration _, .enumeration _ => true
            | _, _ => false)
    | .temporal slots =>
      let operands := slots.flatMap (·.references)
      operands.all fun ref => (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
        declaration.toTemporalField? == some ref.field &&
          declaration.toTemporalTargetPolicy?.any fun policy => operands.head?.any fun first =>
            (model.lookupUniqueId first.field.id).toOption.any fun firstDeclaration =>
              firstDeclaration.toTemporalTargetPolicy?.any (fun other => other.format == policy.format)

end A12Kernel
