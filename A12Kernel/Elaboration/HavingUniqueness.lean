import A12Kernel.Elaboration.HavingFieldValueList
import A12Kernel.Elaboration.FieldEntityAdmission

namespace A12Kernel

/-- Whole-list admission reuses the ordinary uniqueness categories, after direct-list shape
and category-read gates. One temporal format is required independently of temporal kind (spec/07 §5). -/
def elaborateHavingUniqueness (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingDirectFieldSource) :
    Except CorrelationElabError HavingUniqueness := do
  let checked ← elaborateHavingDirectFieldSource model declaringGroup candidateLevels outerLevels source
    .deferCandidate (requireStored := true) |>.mapError .fieldFill
  let declarations := checked.operands.map (·.declaration)
  if let some refusal := firstExpandedKindRefusal? declarations then throw (.uniquenessKind refusal.path)
  let .category category := checked.first.declaration.policy.kind.surfaceKind.fieldListAdmission | throw .incoherentCore
  if let some refusal := firstExpandedCategoryMismatch? category declarations then throw (.membershipBaseType refusal.path)
  match category with
  | .number => return .number (← checked.operands.mapM fun operand => do
      let some field := operand.declaration.toNumberField? | throw .incoherentCore
      pure { origin := operand.origin, field })
  | .string | .enumeration => return .token (← checked.operands.mapM fun operand => do
      let some (field, _) := operand.declaration.toTextFieldComparison? | throw .incoherentCore
      pure { origin := operand.origin, operand := field })
  | .temporal =>
      let some policy := checked.first.declaration.toTemporalTargetPolicy? | throw .incoherentCore
      let operands ← checked.operands.mapM fun operand => do
        let some other := operand.declaration.toTemporalTargetPolicy? | throw .incoherentCore
        if other.format != policy.format then throw (.uniquenessFormat operand.declaration.path)
        let some field := operand.declaration.toTemporalField? | throw .incoherentCore
        pure ({ origin := operand.origin, field } : HavingTemporalRef)
      pure (.temporal operands)

def HavingUniqueness.wellFormedForEnvironments (source : HavingUniqueness) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  let references := source.references
  references.length >= 2 && references.eraseDups.length == references.length &&
    references.all (fun ref => (model.lookupUniqueId ref.field).toOption.any fun declaration =>
      declaration.repetitionBoundBy (ref.origin.availableLevels candidateLevels outerLevels)) &&
    match source with
    | .number operands => operands.all fun ref => (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
        (FlatField.number ref.field).matchesDecl declaration
    | .token operands => operands.all fun ref => (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
        declaration.toTextFieldComparison?.any (fun (operand, _) => operand == ref.operand) &&
          operands.head?.any (fun first => match first.operand, ref.operand with
            | .string _, .string _ | .enumeration _, .enumeration _ => true
            | _, _ => false)
    | .temporal operands => operands.all fun ref => (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
        declaration.toTemporalField? == some ref.field &&
          declaration.toTemporalTargetPolicy?.any fun policy => operands.head?.any fun first =>
            (model.lookupUniqueId first.field.id).toOption.any fun firstDeclaration =>
              firstDeclaration.toTemporalTargetPolicy?.any (fun other => other.format == policy.format)

end A12Kernel
