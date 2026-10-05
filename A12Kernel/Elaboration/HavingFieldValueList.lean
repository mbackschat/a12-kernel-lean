import A12Kernel.Elaboration.CorrelationSurface
import A12Kernel.Elaboration.Flat.FieldValueRead

namespace A12Kernel

private def membershipMultiplicity (operator : ComputationValueListOperator) (subjects : Nat) : Bool :=
  match operator with | .scalar _ => subjects == 1 | .quantified _ => subjects > 0

private def tokenLiteralAllowed (model : FlatModel) (subjects : List HavingStringRef) (value : String) : Bool :=
  subjects.any fun ref => match ref.operand with
    | .string _ => true
    | .enumeration operand => (model.lookupUniqueId operand.field.id).toOption.any fun declaration =>
        (model.checkedEnumerationOperandIn? declaration.repeatableScope operand).any fun checked =>
          checked.declaration.literalAllowed checked.projection value

private def tokenReferencesWellFormed (model : FlatModel) (candidateLevels outerLevels : List RepeatableLevel)
    (references : List HavingStringRef) : Bool :=
  !references.isEmpty && references.eraseDups.length == references.length &&
    references.all (fun ref =>
      let scope := ref.origin.availableLevels candidateLevels outerLevels
      match ref.operand with
      | .string _ => model.directComparableIn? scope ref.operand == some .plainString
      | .enumeration operand => (model.checkedEnumerationOperandIn? scope operand).isSome) &&
    references.all (fun ref => references.head?.any fun first =>
      match first.operand, ref.operand with
      | .string _, .string _ | .enumeration _, .enumeration _ => true
      | _, _ => false)

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
        tokenReferencesWellFormed model candidateLevels outerLevels (subjects ++ members)
  | .tokenLiterals subjects values =>
      !values.isEmpty && tokenReferencesWellFormed model candidateLevels outerLevels subjects &&
        values.all (tokenLiteralAllowed model subjects) &&
        (match operator with | .quantified _ => true | .scalar _ => false)

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


private def resolvedMembershipOperands (written : List SurfaceHavingDirectFieldOperand) (declarations : List FlatFieldDecl) : List (ResolvedHavingDirectFieldOperand model) :=
    (written.zip declarations).map fun (reference, declaration) =>
      ({ origin := reference.origin, declaration, form := reference.form } : ResolvedHavingDirectFieldOperand model)


private def checkMembershipDuplicates (operands : List (ResolvedHavingDirectFieldOperand model)) : Except CorrelationElabError Unit := do
    if let some duplicate := firstDuplicateResolvedHavingDirectField? operands then
      throw (CorrelationElabError.fieldFill (.duplicateOperand duplicate.field))

private def checkMembershipKinds (kind : SurfaceScalarKind) (declarations : List FlatFieldDecl) : Except CorrelationElabError Unit := do
    if let some other := declarations.find? (fun declaration => !kind.sharesValueListBaseType declaration.policy.kind.surfaceKind) then
      throw (CorrelationElabError.membershipBaseType other.path)

private def checkMembershipValues (operands : List (ResolvedHavingDirectFieldOperand model)) : Except CorrelationElabError Unit := do
    for operand in operands do
      if let some error := operand.declaration.projectedReadRefusal? (membershipProjection operand.form) then
        throw (CorrelationElabError.resolve error)

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
  let fields := resolvedMembershipOperands (model := model) writtenSubjects subjectDecls
  let values := resolvedMembershipOperands (model := model) writtenMembers memberDecls
  if let .quantified _ := operator then checkMembershipDuplicates fields
  let some first := subjectDecls.head? | throw .incoherentCore
  let kind := first.policy.kind.surfaceKind
  checkMembershipKinds kind subjectDecls
  if kind != .number && kind != .string && kind != .enumeration then throw (.membershipKind first.path)
  checkMembershipValues fields
  if let .quantified _ := operator then checkMembershipDuplicates values
  checkMembershipKinds kind memberDecls
  checkMembershipDuplicates (fields ++ values)
  checkMembershipValues values
  if kind == .number then
    let number (operand : ResolvedHavingDirectFieldOperand model) := do
      let some field := operand.declaration.toNumberField? | throw CorrelationElabError.incoherentCore
      pure ({ origin := operand.origin, field } : HavingNumberRef)
    return .number (← fields.mapM number) (← values.mapM number)
  return .token (← fields.mapM membershipText) (← values.mapM membershipText)

/-- A plural literal list checks every field read before list gates and admits Enumeration values
against the union of the selected domains (spec/06 §B.3). -/
def elaborateHavingTokenLiteralList (model : FlatModel) (subjects : SurfaceHavingDirectFieldSource)
    (values : List String)
    (readEntity : SurfaceHavingDirectFieldOperand → Except CorrelationElabError FlatFieldDecl) :
    Except CorrelationElabError HavingFieldValueList := do
  let written := subjects.first :: subjects.rest
  let declarations ← written.mapM readEntity
  let fields := resolvedMembershipOperands (model := model) written declarations
  checkMembershipDuplicates fields
  if values.isEmpty then throw .incoherentCore
  let some first := declarations.head? | throw .incoherentCore
  let kind := first.policy.kind.surfaceKind
  checkMembershipKinds kind declarations
  if kind != .number && kind != .string && kind != .enumeration then throw (.membershipKind first.path)
  if kind == .number then throw (.membershipStringLiteralKind first.path)
  checkMembershipValues fields
  let operands ← fields.mapM membershipText
  if let some value := values.find? fun value => !tokenLiteralAllowed model operands value then
    throw (.text (.enumerationOperand first.path (.invalidLiteral value)))
  pure (.tokenLiterals operands values)

end A12Kernel
