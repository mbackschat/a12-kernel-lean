import A12Kernel.Elaboration.CorrelationSurface
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.HavingEntityList

namespace A12Kernel

private def membershipMultiplicity (operator : ComputationValueListOperator) (subjects : Nat) : Bool :=
  match operator with | .scalar _ => subjects == 1 | .quantified _ => subjects > 0

private def tokenLiteralAllowed (model : FlatModel) (subjects : List HavingStringRef) (value : String) : Bool :=
  subjects.any fun ref => match ref.operand with
    | .string _ => true
    | .enumeration operand => (model.lookupUniqueId operand.field.id).toOption.any fun declaration =>
        (model.checkedEnumerationOperandIn? declaration.repeatableScope operand).any fun checked =>
          checked.declaration.literalAllowed checked.projection value

private def membershipSlotsUnique [BEq Ref] (origin : Ref → HavingOrigin)
    (slots : List (HavingFieldListSlot Ref)) : Bool :=
  (firstDuplicateInEncounterOrder? (fun slot => match slot with
    | .direct ref => some (Sum.inl ref : Sum Ref (HavingOrigin × GroupPath))
    | .extent (.group source) (ref :: _) => some (.inr (origin ref, source.path))
    | _ => none) slots).isNone

private def tokenReferencesWellFormed (model : FlatModel)
    (slots : List (HavingFieldListSlot HavingStringRef)) : Bool :=
  let references := slots.flatMap (·.references)
  slots.all (fun slot => slot.references.all (fun ref =>
    (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
      -- A field star preserves its authored category; a group expansion always reads stored
      -- tokens (spec/06 §B.3), so only group extents require the stored comparison here.
      (match slot with
        | .extent (.group _) _ | .extent (.starredGroup _ _) _ =>
            declaration.toTextFieldComparison?.any (fun (operand, _) => operand == ref.operand)
        | _ => true) &&
      match ref.operand with
      | .string _ => model.directComparableIn? declaration.repeatableScope ref.operand == some .plainString
      | .enumeration operand => (model.checkedEnumerationOperandIn? declaration.repeatableScope operand).isSome)) &&
  references.all (fun ref => references.head?.any fun first =>
    match first.operand, ref.operand with
    | .string _, .string _ | .enumeration _, .enumeration _ => true
    | _, _ => false)

def HavingFieldValueList.wellFormedForEnvironments (source : HavingFieldValueList)
    (operator : ComputationValueListOperator) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  source.presenceSlots.all (·.wellFormedForEnvironments model candidateLevels outerLevels) &&
  match source with
  | .number subjects members =>
      havingTypedEntitySlotsDisjoint model id (fun _ => none) source.presenceSlots &&
      membershipMultiplicity operator subjects.length && !members.isEmpty &&
      (match operator with | .scalar _ => (subjects ++ members).all (·.isDirect) | .quantified _ => true) &&
      membershipSlotsUnique (·.origin) (subjects ++ members) &&
      ((subjects ++ members).flatMap (·.references)).all fun ref =>
        (model.lookupUniqueId ref.field.id).toOption.any fun declaration => (FlatField.number ref.field).matchesDecl declaration
  | .token subjects members =>
      havingTypedEntitySlotsDisjoint model
        (fun (ref : HavingStringRef) => { origin := ref.origin, field := ref.field.id })
        HavingStringRef.categoryIdentity? (subjects ++ members) &&
      membershipMultiplicity operator subjects.length && !members.isEmpty &&
      (match operator with | .scalar _ => (subjects ++ members).all (·.isDirect) | .quantified _ => true) &&
      membershipSlotsUnique (·.origin) (subjects ++ members) &&
      tokenReferencesWellFormed model (subjects ++ members)
  | .tokenLiterals subjects values =>
      havingTypedEntitySlotsDisjoint model
        (fun (ref : HavingStringRef) => { origin := ref.origin, field := ref.field.id })
        HavingStringRef.categoryIdentity? subjects &&
      !subjects.isEmpty && !values.isEmpty && membershipSlotsUnique (·.origin) subjects &&
      tokenReferencesWellFormed model subjects &&
      values.all (tokenLiteralAllowed model (subjects.flatMap (·.references))) &&
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

/-- Scalar members ask their read gates before the subject's kind gate (spec/06 §B.4). -/
private def elaborateHavingScalarFieldValueList (model : FlatModel)
    (subjects members : SurfaceHavingDirectFieldSource)
    (readEntity readValue : SurfaceHavingDirectFieldOperand → Except CorrelationElabError FlatFieldDecl) :
    Except CorrelationElabError HavingFieldValueList := do
  let writtenSubjects := subjects.first :: subjects.rest
  let writtenMembers := members.first :: members.rest
  if !subjects.rest.isEmpty then throw .incoherentCore
  let (subject, memberDecls) ← resolveScalarMembershipReads readEntity readValue
    (fun subject error => match subject.form, error with
      | .stored, .resolve (.groupInFieldValueRead _ none _) => true
      | _, _ => false) subjects.first writtenMembers
  let subjectDecls := [subject]
  let fields := resolvedMembershipOperands (model := model) writtenSubjects subjectDecls
  let values := resolvedMembershipOperands (model := model) writtenMembers memberDecls
  let some first := subjectDecls.head? | throw .incoherentCore
  let kind := first.policy.kind.surfaceKind
  checkMembershipKinds kind subjectDecls
  if kind != .number && kind != .string && kind != .enumeration then throw (.membershipKind first.path)
  checkMembershipValues fields
  checkMembershipKinds kind memberDecls
  checkMembershipDuplicates (fields ++ values)
  checkMembershipValues values
  if kind == .number then
    let number (operand : ResolvedHavingDirectFieldOperand model) := do
      let some field := operand.declaration.toNumberField? | throw CorrelationElabError.incoherentCore
      pure ({ origin := operand.origin, field } : HavingNumberRef)
    return .number ((← fields.mapM number).map .direct) ((← values.mapM number).map .direct)
  return .token ((← fields.mapM membershipText).map .direct) ((← values.mapM membershipText).map .direct)

private def directSource (source : SurfaceHavingEntitySource) : Except CorrelationElabError SurfaceHavingDirectFieldSource := do
  let operands ← (source.first :: source.rest).mapM fun
    | .entity ref => pure ref
    | _ => throw .incoherentCore
  let first :: rest := operands | throw .incoherentCore
  pure { first, rest }

private def certifyMembershipSlots (kind : SurfaceScalarKind)
    (slots : List (HavingFieldListSlot (ResolvedHavingDirectFieldOperand model))) :
    Except CorrelationElabError (Sum (List (HavingFieldListSlot HavingNumberRef)) (List (HavingFieldListSlot HavingStringRef))) := do
  if kind == .number then
    return .inl (← slots.mapM fun slot => slot.mapM fun operand => do
      let some field := operand.declaration.toNumberField? | throw .incoherentCore
      pure { origin := operand.origin, field })
  return .inr (← slots.mapM fun slot => slot.mapM membershipText)

/-- Resolve both sides before the staged list gates; cross-side repeats follow subject value
validation and member base types, as in spec/06 §B.3. Scalar forms retain field-read admission. -/
def elaborateHavingFieldValueList (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (operator : ComputationValueListOperator)
    (subjects members : SurfaceHavingEntitySource)
    (readEntity readValue : SurfaceHavingDirectFieldOperand → Except CorrelationElabError FlatFieldDecl) :
    Except CorrelationElabError HavingFieldValueList := do
  if let .scalar _ := operator then
    return ← elaborateHavingScalarFieldValueList model (← directSource subjects) (← directSource members) readEntity readValue
  let fields ← resolveHavingEntityListOperands model declaringGroup candidateLevels outerLevels subjects
  let values ← resolveHavingEntityListOperands model declaringGroup candidateLevels outerLevels members
  let fieldSlots ← havingResolvedEntitySlots fields
  let valueSlots ← havingResolvedEntitySlots values
  let fieldRefs := fieldSlots.flatMap (·.references)
  let valueRefs := valueSlots.flatMap (·.references)
  checkHavingEntityDuplicates fields
  checkHavingEntityRoots fields
  let some first := fieldRefs.head? | throw .incoherentCore
  let kind := first.declaration.policy.kind.surfaceKind
  checkMembershipKinds kind (fieldRefs.map (·.declaration))
  if kind != .number && kind != .string && kind != .enumeration then throw (.membershipKind first.declaration.path)
  checkMembershipValues fieldRefs
  checkHavingEntityDuplicates values
  checkHavingEntityRoots values
  checkMembershipKinds kind (valueRefs.map (·.declaration))
  checkHavingEntityDuplicates (fields ++ values)
  checkMembershipValues valueRefs
  match ← certifyMembershipSlots kind fieldSlots, ← certifyMembershipSlots kind valueSlots with
  | .inl subjects, .inl members => pure (.number subjects members)
  | .inr subjects, .inr members => pure (.token subjects members)
  | _, _ => throw .incoherentCore

/-- Literal domains use the union of all projected declarations, while authored slots retain
scope and expansion boundaries (spec/06 §B.3). -/
def elaborateHavingTokenLiteralList (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel) (subjects : SurfaceHavingEntitySource)
    (values : List String) : Except CorrelationElabError HavingFieldValueList := do
  let operands ← resolveHavingEntityListOperands model declaringGroup candidateLevels outerLevels subjects
  let slots ← havingResolvedEntitySlots operands
  let fields := slots.flatMap (·.references)
  checkHavingEntityDuplicates operands
  checkHavingEntityRoots operands
  if values.isEmpty then throw .incoherentCore
  let some first := fields.head? | throw .incoherentCore
  let kind := first.declaration.policy.kind.surfaceKind
  checkMembershipKinds kind (fields.map (·.declaration))
  if kind != .number && kind != .string && kind != .enumeration then throw (.membershipKind first.declaration.path)
  if kind == .number then throw (.membershipStringLiteralKind first.declaration.path)
  checkMembershipValues fields
  let operands ← slots.mapM fun slot => slot.mapM membershipText
  if let some value := values.find? fun value => !tokenLiteralAllowed model (operands.flatMap (·.references)) value then
    throw (.text (.enumerationOperand first.declaration.path (.invalidLiteral value)))
  pure (.tokenLiterals operands values)

end A12Kernel
