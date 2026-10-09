import A12Kernel.Elaboration.HavingFieldValueList
import A12Kernel.Elaboration.HavingEntityList

namespace A12Kernel

/-- Uniqueness checks the complete kind/format walk before base agreement and raw-value access
(CheckEntityListenUtils.checkOnlyStringEnumNumberOrDateWithSameFormat; spec/07 §5). -/
def checkHavingUniquenessDeclarations (declarations : List FlatFieldDecl) :
    Except CorrelationElabError Unit := do
  let mut format : Option String := none
  for declaration in declarations do
    match declaration.policy.kind.surfaceKind.fieldListAdmission with
    | .refusedByKind => throw (.uniquenessKind declaration.path)
    | .category .temporal =>
        let some policy := declaration.toTemporalTargetPolicy? | throw .incoherentCore
        if format.any (· != policy.format) then throw (.uniquenessFormat declaration.path)
        format := some policy.format
    | .category _ => pure ()
  let some first := declarations.head? | throw .incoherentCore
  let .category category := first.policy.kind.surfaceKind.fieldListAdmission | throw .incoherentCore
  if let some refusal := firstExpandedCategoryMismatch? category declarations then throw (.membershipBaseType refusal.path)
  if let some declaration := declarations.find? (·.isRawString) then
    throw (.resolve (.rawFieldValueRead declaration.path))

/-- The ordinary category and exact-format gates inspect the complete declaration expansion;
runtime keeps the authored slots for ordered extent acquisition (spec/07 §5). -/
def elaborateHavingUniqueness (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (source : SurfaceHavingEntitySource) :
    Except CorrelationElabError HavingUniqueness := do
  let checked ← elaborateHavingEntityList model declaringGroup candidateLevels outerLevels source
  let declarations := checked.flatMap (fun slot => slot.references.map (·.declaration))
  checkHavingUniquenessDeclarations declarations
  let some first := declarations.head? | throw .incoherentCore
  let .category category := first.policy.kind.surfaceKind.fieldListAdmission | throw .incoherentCore
  match category with
  | .number => return .number (← checked.mapM fun slot => slot.mapM fun operand => do
      let some field := operand.declaration.toNumberField? | throw .incoherentCore
      pure { origin := operand.origin, field })
  | .string | .enumeration => return .token (← checked.mapM fun slot => slot.mapM fun operand => do
      let some (field, _) := operand.declaration.toTextFieldComparison? | throw .incoherentCore
      pure { origin := operand.origin, operand := field })
  | .temporal =>
      let operands ← checked.mapM fun slot => slot.mapM fun operand => do
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
