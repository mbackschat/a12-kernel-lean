import A12Kernel.Elaboration.HavingEntityList
import A12Kernel.Elaboration.DateRangeBound

namespace A12Kernel

private inductive HavingSelectedProfile where
  | text
  | boolean
  | dateRange (format : DateRangeInputFormat)
  deriving DecidableEq

private def HavingSelectedRef.profile? (reference : HavingSelectedRef) (model : FlatModel) :
    Option HavingSelectedProfile := do
  let declaration ← (model.lookupUniqueId reference.fieldId).toOption
  if declaration.fieldValueReadRefusal?.isSome then none else
    match reference with
    | .text reference =>
        if declaration.textComparisonProfileFor? reference.operand |>.isSome then some .text else none
    | .boolean _ field => if declaration.policy.kind == .boolean && declaration.id == field.id then some .boolean else none
    | .dateRange _ field => do
        let (_, _, format) ← model.dateRangeSourceProfile field
        pure (.dateRange format)

private def HavingSelectedOperand.profile? (operand : HavingSelectedOperand) (model : FlatModel) :
    Option HavingSelectedProfile :=
  match operand with
  | .text _ => some .text
  | .boolean _ => some .boolean
  | .field reference => reference.profile? model
  | .firstFilled slots => do
      let first :: rest := slots.flatMap (·.references) | none
      let profile ← first.profile? model
      if rest.all (fun reference => reference.profile? model == some profile) then some profile else none

def HavingSelectedOperand.wellFormed (operand : HavingSelectedOperand) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  (operand.profile? model).isSome &&
    operand.presenceSlots.all (·.wellFormedForEnvironments model candidateLevels outerLevels) &&
    match operand with
    | .firstFilled slots =>
        havingTypedEntityListWellFormed model candidateLevels outerLevels HavingSelectedRef.presence slots
          (fun | .text ref => ref.categoryIdentity? | _ => none) &&
          slots.all fun slot => slot.references.all fun reference =>
            match slot, reference with
            | .extent (.group _) _, .text ref | .extent (.starredGroup _ _) _, .text ref =>
                (model.lookupUniqueId ref.field.id).toOption.any fun declaration =>
                  declaration.toTextFieldComparison?.any (fun (operand, _) => operand == ref.operand)
            | _, _ => true
    | _ => true

def HavingSelectedComparison.wellFormed (source : HavingSelectedComparison) (model : FlatModel)
    (candidateLevels outerLevels : List RepeatableLevel) : Bool :=
  source.left.wellFormed model candidateLevels outerLevels &&
    source.right.wellFormed model candidateLevels outerLevels &&
    (match source.left, source.right with | .firstFilled _, _ | _, .firstFilled _ => true | _, _ => false) &&
    match source.left.profile? model, source.right.profile? model with
    | some .text, some .text | some .boolean, some .boolean => true
    | some (.dateRange left), some (.dateRange right) => left.components == right.components
    | _, _ => false

def resolveHavingSelectedReference (reference : ResolvedHavingDirectFieldOperand model) :
    Except CorrelationElabError HavingSelectedRef := do
  if reference.form == .stored then
    match reference.declaration.policy.kind with
    | .boolean => return .boolean reference.origin { id := reference.declaration.id }
    | .dateRange => return .dateRange reference.origin { id := reference.declaration.id }
    | _ => pure ()
  let profile := match reference.form with
    | .stored => reference.declaration.toTextFieldComparison?
    | .projected category => reference.declaration.toEnumerationTextFieldComparison? (.category category)
  let some (operand, _) := profile | throw .numericExpressionUnsupported
  pure (.text { origin := reference.origin, operand })

def elaborateHavingSelectedComparison (model : FlatModel) (declaringGroup : GroupPath)
    (candidateLevels outerLevels : List RepeatableLevel)
    (resolve : SurfaceHavingStringRef → Except CorrelationElabError FlatFieldDecl)
    (operator : SurfaceComparisonOp) (left right : SurfaceHavingSelectedOperand) :
    Except CorrelationElabError HavingSelectedComparison := do
  let operand : SurfaceHavingSelectedOperand → Except CorrelationElabError HavingSelectedOperand
    | .text value => pure (.text value)
    | .boolean value => pure (.boolean value)
    | .field reference => do
        let declaration ← resolve reference
        .field <$> resolveHavingSelectedReference (model := model) {
          origin := reference.origin, declaration
          form := match reference.projectionRef with | .stored => .stored | .category name => .projected name }
    | .firstFilled source => do
        let slots ← resolveHavingProjectedEntityList model declaringGroup candidateLevels outerLevels source
        .firstFilled <$> slots.mapM (·.mapM resolveHavingSelectedReference)
  let first ← operand left
  let second ← operand right
  let entry (source : HavingSelectedOperand) := do
    if !source.wellFormed model candidateLevels outerLevels then throw CorrelationElabError.numericExpressionUnsupported
    let some profile := source.profile? model | throw .incoherentCore
    let kind : SurfaceScalarKind := match profile with
      | .text => .string | .boolean => .boolean | .dateRange _ => .dateRange
    pure (match source with
      | .text _ | .boolean _ => ComparisonEntryOperand.literal kind
      | .field _ => .field kind
      | .firstFilled _ => .expression kind)
  let leftEntry ← entry first
  let rightEntry ← entry second
  discard <| (checkComparisonEntry (if operator.toEquality?.isSome then .equality else .ordering)
    leftEntry rightEntry).mapError .comparisonEntry
  let some equality := operator.toEquality? | throw .incoherentCore
  let result : HavingSelectedComparison := { operator := equality, left := first, right := second }
  if !result.wellFormed model candidateLevels outerLevels then throw .numericExpressionUnsupported
  pure result

end A12Kernel
