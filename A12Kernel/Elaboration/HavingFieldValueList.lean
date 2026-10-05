import A12Kernel.Elaboration.CorrelationSurface
import A12Kernel.Elaboration.Flat.FieldValueRead

namespace A12Kernel

private def membershipMultiplicity (operator : ComputationValueListOperator) (subjects : Nat) : Bool :=
  match operator with | .scalar _ => subjects == 1 | .quantified _ => subjects > 0

def HavingFieldValueList.wellFormedForEnvironments (source : HavingFieldValueList)
    (operator : ComputationValueListOperator) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  match source with
  | .number subjects members =>
      membershipMultiplicity operator subjects.length && !members.isEmpty &&
        (subjects ++ members).eraseDups.length == (subjects ++ members).length &&
        (subjects ++ members).all fun ref => (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
          (FlatField.number ref.field).matchesDecl declaration &&
            declaration.repetitionBoundBy (ref.origin.availableLevels candidateLevels outerLevels)
  | .token subjects members =>
      membershipMultiplicity operator subjects.length && !members.isEmpty &&
        (subjects ++ members).eraseDups.length == (subjects ++ members).length &&
        (subjects ++ members).all (fun ref =>
          let scope := ref.origin.availableLevels candidateLevels outerLevels
          match ref.operand with
          | .string _ => model.directComparableIn? scope ref.operand == some .plainString
          | .enumeration operand => (model.checkedEnumerationOperandIn? scope operand).isSome) &&
        (subjects ++ members).all fun ref => subjects.head?.any fun first =>
          match first.operand, ref.operand with
          | .string _, .string _ | .enumeration _, .enumeration _ => true
          | _, _ => false

private def membershipProjection : FieldEntityReadForm → EnumerationProjectionRef
  | .stored => .stored
  | .projected category => .category category

private def membershipText (operand : ResolvedHavingDirectFieldOperand model) :
    Except CorrelationElabError HavingStringRef := do
  let profile := match operand.form with
    | .stored => operand.declaration.toTextFieldComparison?
    | .projected category => operand.declaration.toEnumerationTextFieldComparison? (.category category)
  let some (field, _) := profile | throw .incoherentCore
  pure { origin := operand.origin, operand := field }

/-- Scalar members ask their read gates before the subject's kind gate; plural lists retain
side-local and cross-side identity checks around value validation (spec/06 §B.3–B.5). -/
def elaborateHavingFieldValueList (model : FlatModel) (operator : ComputationValueListOperator)
    (subjects members : SurfaceHavingDirectFieldSource)
    (readEntity readValue : SurfaceHavingDirectFieldOperand → Except CorrelationElabError FlatFieldDecl) :
    Except CorrelationElabError HavingFieldValueList := do
  let writtenSubjects := subjects.first :: subjects.rest
  let writtenMembers := members.first :: members.rest
  let (subjectDecls, memberDecls) ← match operator with
    | .scalar _ => do
        if !subjects.rest.isEmpty then throw .incoherentCore
        let (subject, members) ← resolveScalarMembershipReads readEntity readValue
          (fun subject error => match subject.form, error with
            | .stored, .resolve (.groupInFieldValueRead _ none _) => true
            | _, _ => false) subjects.first writtenMembers
        pure ([subject], members)
    | .quantified _ => do
        pure (← writtenSubjects.mapM readEntity, ← writtenMembers.mapM readEntity)
  let resolved (written : List SurfaceHavingDirectFieldOperand) (declarations : List FlatFieldDecl) :=
    (written.zip declarations).map fun (reference, declaration) =>
      ({ origin := reference.origin, declaration, form := reference.form } : ResolvedHavingDirectFieldOperand model)
  let fields := resolved writtenSubjects subjectDecls
  let values := resolved writtenMembers memberDecls
  let checkDuplicates (operands : List (ResolvedHavingDirectFieldOperand model)) := do
    if let some duplicate := firstDuplicateResolvedHavingDirectField? operands then
      throw (CorrelationElabError.fieldFill (.duplicateOperand duplicate.field))
  if let .quantified _ := operator then checkDuplicates fields
  let some first := subjectDecls.head? | throw .incoherentCore
  let kind := first.policy.kind.surfaceKind
  let checkKinds (declarations : List FlatFieldDecl) := do
    if let some other := declarations.find? (fun declaration => !kind.sharesValueListBaseType declaration.policy.kind.surfaceKind) then
      throw (CorrelationElabError.membershipBaseType other.path)
  checkKinds subjectDecls
  if kind != .number && kind != .string && kind != .enumeration then throw (.membershipKind first.path)
  let checkValues (operands : List (ResolvedHavingDirectFieldOperand model)) := do
    for operand in operands do
      if let some error := operand.declaration.projectedReadRefusal? (membershipProjection operand.form) then
        throw (CorrelationElabError.resolve error)
  checkValues fields
  if let .quantified _ := operator then checkDuplicates values
  checkKinds memberDecls
  checkDuplicates (fields ++ values)
  checkValues values
  if kind == .number then
    let number (operand : ResolvedHavingDirectFieldOperand model) := do
      let some field := operand.declaration.toNumberField? | throw CorrelationElabError.incoherentCore
      pure ({ origin := operand.origin, field } : HavingNumberRef)
    return .number (← fields.mapM number) (← values.mapM number)
  return .token (← fields.mapM membershipText) (← values.mapM membershipText)

end A12Kernel
