import A12Kernel.Elaboration.Flat.Condition.SurfaceSupport
import A12Kernel.Elaboration.Flat.FieldValueRead

/-! # Flat-condition surface lowering -/

namespace A12Kernel

private def elaborateEnumerationCore (declaration : FlatFieldDecl)
    (op : SurfaceComparisonOp) (projectionRef : EnumerationProjectionRef)
    (expected : String) : Except ElabError FlatCondition := do
  let equality ← match op.toEquality? with
    | some equality => pure equality
    | none => throw (.unsupportedOperator op)
  match declaration.policy.kind, declaration.enumeration with
  | .enumeration, some source =>
      match elaborateEnumeration source with
      | .error _ => throw .incoherentCore
      | .ok checked =>
          match classifyEnumerationLiteral checked projectionRef equality expected with
          | .rejected error => throw (.enumerationOperand declaration.path error)
          | .accepted projection =>
              pure (.compare (.enumeration equality {
                field := { id := declaration.id }
                projectionRef
                projection } expected))
  | kind, _ =>
      throw (.literalKindMismatch declaration.path .enumeration kind.surfaceKind)

private def finishTextFieldComparison (op : SurfaceComparisonOp)
    (leftPath rightPath : List String)
    (left right : FlatTextFieldOperand × DirectComparableField) :
    Except ElabError FlatCondition := do
  let equality ← match op.toEquality? with
    | some equality => pure equality
    | none => throw (.unsupportedOperator op)
  match classifyDirectFieldComparison left.2 right.2 with
  | .accepted => pure (.compare (.textFields equality left.1 right.1))
  | .rejected error => throw (.enumerationComparability leftPath rightPath error)

/-- Resolve one direct nonrepeatable stored/category Enumeration operand with its exact checked projection and runtime core. -/
def elaborateEnumerationFieldOperand (model : FlatModel)
    (declaringGroup : GroupPath) (surface : SurfaceTextFieldOperand)
    (writtenGroup : GroupPath := declaringGroup) :
    Except ElabError
      (List String × CheckedEnumerationProjection × FlatEnumerationOperand) := do
  let projectionRef := surface.projectionRef
  let declaration ←
    (model.resolveNonrepeatableFieldUnchecked declaringGroup surface.reference writtenGroup).mapError .resolve
  match declaration.policy.kind, declaration.enumeration with
  | .enumeration, some source =>
      match elaborateEnumeration source with
      | .error _ => throw .incoherentCore
      | .ok checked =>
          match checkEnumerationProjection checked projectionRef with
          | .error error => throw (.enumerationOperand declaration.path error)
          | .ok projection =>
              pure (declaration.path, projection, {
                field := { id := declaration.id }
                projectionRef := projection.projectionRef
                projection := projection.projection })
  | kind, _ =>
      throw (.textFieldOperandKindMismatch declaration.path kind.surfaceKind)

private def elaborateEnumerationLiteralList (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surface : SurfaceTextFieldOperand)
    (values : List String) : Except ElabError FlatEnumerationOperand := do
  let (path, checked, operand) ←
    elaborateEnumerationFieldOperand model declaringGroup surface writtenGroup
  if values.isEmpty then
    throw (.emptyValueList path)
  else
    match values.find? fun value =>
        !checked.declaration.literalAllowed checked.projection value with
    | some value => throw (.enumerationOperand path (.invalidLiteral value))
    | none => pure operand

/-- A multi-field list's operand, read through a field resolver. A path naming a group is an operand
    the Kernel expands, so `(Ledger, Other In "a")` draws the base-type class of the group's fields
    beside the String ([checkpoint](../../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions));
    this flat route cannot expand it and refuses without the entity class a field resolver reports. A
    membership's subject and members are read before any list operand, so none reaches here as a
    group. -/
private def FlatModel.resolveFlatListOperand (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (surface : SurfaceFieldPath) : Except ElabError FlatFieldDecl :=
  (model.resolveNonrepeatableFieldUnchecked declaringGroup surface writtenGroup).mapError fun miss =>
    match displaceGroupMiss miss (model.ruleGroupRead declaringGroup writtenGroup surface) with
    | .groupInFieldValueRead group _ _ => .groupOperandOutsideTokenRoute group
    | other => .resolve other

private abbrev ElaboratedEnumerationOperand :=
  List String × CheckedEnumerationProjection × FlatEnumerationOperand

private def duplicateElaboratedEnumerationOperand? :
    List ElaboratedEnumerationOperand →
      Option (List String × EnumerationProjectionRef)
  | [] => none
  | current :: remaining =>
      if remaining.any fun candidate => candidate.2.2 == current.2.2 then
        some (current.1, current.2.2.projectionRef)
      else
        duplicateElaboratedEnumerationOperand? remaining

private def elaborateEnumerationOperandList (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surfaces : List SurfaceTextFieldOperand)
    (emptyError : ElabError) : Except ElabError (List ElaboratedEnumerationOperand) := do
  if surfaces.isEmpty then
    throw emptyError
  surfaces.mapM fun surface => do
    if let .direct reference := surface then
      discard <| model.resolveFlatListOperand declaringGroup writtenGroup reference
    elaborateEnumerationFieldOperand model declaringGroup surface writtenGroup

private def rejectDuplicateEnumerationOperands
    (resolved : List ElaboratedEnumerationOperand) : Except ElabError Unit :=
  match duplicateElaboratedEnumerationOperand? resolved with
  | some (path, projectionRef) =>
      throw (.duplicateValueListField path projectionRef)
  | none => pure ()

private def elaborateEnumerationLiteralFieldList (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surfaces : List SurfaceTextFieldOperand)
    (values : List String) : Except ElabError (List FlatEnumerationOperand) := do
  let resolved ← elaborateEnumerationOperandList model declaringGroup writtenGroup surfaces
    .emptyValueListFields
  rejectDuplicateEnumerationOperands resolved
  match resolved with
  | [] => throw .emptyValueListFields
  | first :: remaining =>
      if values.isEmpty then
        throw (.emptyValueList first.1)
      else
        match values.find? fun value =>
            !resolved.any fun entry =>
              entry.2.1.declaration.literalAllowed
                entry.2.1.projection value with
        | some value =>
            throw (.enumerationOperand first.1 (.invalidLiteral value))
        | none => pure ((first :: remaining).map (·.2.2))

private def elaborateEnumerationFieldValueSides (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (fieldSurfaces valueSurfaces : List SurfaceTextFieldOperand) :
    Except ElabError (List FlatEnumerationOperand × List FlatEnumerationOperand) := do
  let fields ← elaborateEnumerationOperandList model declaringGroup writtenGroup fieldSurfaces
    .emptyValueListFields
  let values ← elaborateEnumerationOperandList model declaringGroup writtenGroup valueSurfaces
    .emptyValueListValueFields
  rejectDuplicateEnumerationOperands (fields ++ values)
  pure (fields.map (·.2.2), values.map (·.2.2))

private abbrev ElaboratedStringValueListOperand := List String × FlatTextFieldOperand

private def requireStringValueField (declaration : FlatFieldDecl) :
    Except ElabError FlatStringField :=
  match declaration.toStringValueField? with
  | some field => pure field
  | none =>
      if declaration.isRawString then
        throw (.rawStringValue declaration.path)
      else
        throw (.textFieldOperandKindMismatch declaration.path
          declaration.policy.kind.surfaceKind)

private def duplicateExactValueListOperand? {operand : Type} [BEq operand] :
    List (List String × operand) → Option (List String)
  | [] => none
  | current :: remaining =>
      if remaining.any fun candidate => candidate.2 == current.2 then
        some current.1
      else
        duplicateExactValueListOperand? remaining

private def elaborateStringValueListOperand (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surface : SurfaceFieldPath) :
    Except ElabError ElaboratedStringValueListOperand := do
  let declaration ← model.resolveFlatListOperand declaringGroup writtenGroup surface
  let field ← requireStringValueField declaration
  pure (declaration.path, .string field)

private def elaborateStringLiteralList (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surface : SurfaceFieldPath)
    (values : List String) : Except ElabError FlatTextFieldOperand := do
  let (path, operand) ←
    elaborateStringValueListOperand model declaringGroup writtenGroup surface
  if values.isEmpty then
    throw (.emptyValueList path)
  else
    pure operand

private def elaborateStringValueListOperands (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surfaces : List SurfaceFieldPath)
    (emptyError : ElabError) : Except ElabError (List ElaboratedStringValueListOperand) := do
  if surfaces.isEmpty then
    throw emptyError
  surfaces.mapM (elaborateStringValueListOperand model declaringGroup writtenGroup)

private def rejectDuplicateStringValueListOperands
    (resolved : List ElaboratedStringValueListOperand) : Except ElabError Unit :=
  match duplicateExactValueListOperand? resolved with
  | some path => throw (.duplicateStringValueListField path)
  | none => pure ()

private def elaborateStringLiteralFieldList (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surfaces : List SurfaceFieldPath)
    (values : List String) : Except ElabError (List FlatTextFieldOperand) := do
  let resolved ← elaborateStringValueListOperands model declaringGroup writtenGroup surfaces
    .emptyValueListFields
  rejectDuplicateStringValueListOperands resolved
  match resolved with
  | [] => throw .emptyValueListFields
  | first :: remaining =>
      if values.isEmpty then
        throw (.emptyValueList first.1)
      else
        pure ((first :: remaining).map (·.2))

private def elaborateStringFieldValueSides (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (fieldSurfaces valueSurfaces : List SurfaceFieldPath) :
    Except ElabError (List FlatTextFieldOperand × List FlatTextFieldOperand) := do
  let fields ← elaborateStringValueListOperands model declaringGroup writtenGroup fieldSurfaces
    .emptyValueListFields
  let values ← elaborateStringValueListOperands model declaringGroup writtenGroup valueSurfaces
    .emptyValueListValueFields
  rejectDuplicateStringValueListOperands (fields ++ values)
  pure (fields.map (·.2), values.map (·.2))

private abbrev ElaboratedNumberValueListOperand := List String × FlatNumberField

private def elaborateNumberValueListOperand (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surface : SurfaceFieldPath) :
    Except ElabError ElaboratedNumberValueListOperand := do
  let declaration ← model.resolveFlatListOperand declaringGroup writtenGroup surface
  match declaration.toNumberField? with
  | some operand => pure (declaration.path, operand)
  | none =>
      throw (.literalKindMismatch declaration.path .number
        declaration.policy.kind.surfaceKind)

private def elaborateNumberValueListOperands (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surfaces : List SurfaceFieldPath)
    (emptyError : ElabError) : Except ElabError (List ElaboratedNumberValueListOperand) := do
  if surfaces.isEmpty then
    throw emptyError
  surfaces.mapM (elaborateNumberValueListOperand model declaringGroup writtenGroup)

private def rejectDuplicateNumberValueListOperands
    (resolved : List ElaboratedNumberValueListOperand) : Except ElabError Unit :=
  match duplicateExactValueListOperand? resolved with
  | some path => throw (.duplicateNumberValueListField path)
  | none => pure ()

private def elaborateNumberLiteralMembership (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (surface : SurfaceFieldPath)
    (values : List Int) : Except ElabError (FlatNumberField × List Rat) := do
  let (path, operand) ←
    elaborateNumberValueListOperand model declaringGroup writtenGroup surface
  if values.isEmpty then
    throw (.emptyValueList path)
  pure (operand, values.map Rat.ofInt)

private def elaborateNumberFieldValueSides (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) (fieldSurfaces valueSurfaces : List SurfaceFieldPath) :
    Except ElabError (List FlatNumberField × List FlatNumberField) := do
  let fields ← elaborateNumberValueListOperands model declaringGroup writtenGroup fieldSurfaces
    .emptyValueListFields
  let values ← elaborateNumberValueListOperands model declaringGroup writtenGroup valueSurfaces
    .emptyValueListValueFields
  rejectDuplicateNumberValueListOperands (fields ++ values)
  pure (fields.map (·.2), values.map (·.2))

/-- A scalar membership's subject is an entity rather than a bracket, so it asks the group gate alone
    as it is read, and a category subject the category read's gates. The construct's kind gate follows
    and then its value validation: a partially known Date draws the kind class a full Date draws, and
    a raw String the raw class, on both the literal and the field-valued form
    ([checkpoint](../../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
private def FlatModel.scalarSubjectRead (model : FlatModel) (declaringGroup writtenGroup : GroupPath) :
    SurfaceTextFieldOperand → Except ResolveError FlatFieldDecl
  | .category reference _ => model.resolveCategoryRead declaringGroup reference writtenGroup
  | .direct reference => model.resolveEntityRead declaringGroup reference writtenGroup

/-- A scalar membership's field-valued members are field-value reads, whose gates the Kernel asks as
    each bracket closes, during the parse and so ahead of the subject's kind gate and the member
    list's duplicate and base-type gates
    ([inbound](../../../../docs/SOURCES.md#inbound-2026-09-25f-field-value-read)). A category member
    asks the category read's gates.

    The subject's gates split around the members. A plain subject naming a fixed group or a root is
    refused `MVK_NO_GROUPS_ALLOWED` only after them, by the construct's field check, while an unstarred
    repeatable group's missing-star class, a name resolving to nothing and a category subject's chain
    answer as the subject is read, ahead of them
    ([checkpoint](../../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-remaining-sites),
    [checkpoint](../../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
private def checkScalarMemberReads (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (subject : SurfaceTextFieldOperand) (members : List SurfaceTextFieldOperand) :
    Except ElabError Unit := do
  let groupSubject ← match subject, model.scalarSubjectRead declaringGroup writtenGroup subject with
    | .direct _, .error error@(.groupInFieldValueRead _ none _) => pure (some error)
    | _, .error error => throw (.resolve error)
    | _, .ok _ => pure none
  for member in members do
    discard <| (model.resolveProjectedFieldValueRead declaringGroup member.reference member.projectionRef
      writtenGroup).mapError .resolve
  if let some error := groupSubject then
    throw (.resolve error)

/-- A scalar membership against literals has no members to wait for, so its subject's group gate
    answers first: a fixed group or a root draws the group class and an unstarred repeatable group the
    missing-star class, on the String and the Number form alike
    ([checkpoint](../../../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
private def checkScalarLiteralSubjectRead (model : FlatModel) (declaringGroup writtenGroup : GroupPath)
    (subject : SurfaceTextFieldOperand) : Except ElabError Unit :=
  discard <| (model.scalarSubjectRead declaringGroup writtenGroup subject).mapError .resolve

private def elaborateTextFieldOperand (model : FlatModel)
    (declaringGroup writtenGroup : GroupPath) : SurfaceTextFieldOperand →
      Except ElabError (List String × FlatTextFieldOperand × DirectComparableField)
  | .direct reference => do
      -- A raw String is refused by the read's gate, so no raw declaration reaches the kind arm.
      let declaration ← (model.resolveFieldValueRead declaringGroup reference writtenGroup).mapError .resolve
      match declaration.toTextFieldComparison? with
      | some (operand, profile) => pure (declaration.path, operand, profile)
      | none =>
          throw (.textFieldOperandKindMismatch declaration.path
            declaration.policy.kind.surfaceKind)
  | surface@(.category reference _) => do
      discard <| (model.resolveCategoryRead declaringGroup reference writtenGroup).mapError .resolve
      let (path, _, operand) ←
        elaborateEnumerationFieldOperand model declaringGroup surface writtenGroup
      pure (path, .enumeration operand, .category)

private def elaborateCore (model : FlatModel) (declaringGroup writtenGroup : GroupPath) :
    SurfaceCondition → Except ElabError FlatCondition
  | .fieldFilled reference => do
      let declaration ← (model.resolvePresenceOperand declaringGroup writtenGroup reference
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference writtenGroup)).mapError .resolve
      pure (.fieldFilled declaration.toPresenceField)
  | .fieldNotFilled reference => do
      let declaration ← (model.resolvePresenceOperand declaringGroup writtenGroup reference
        (model.resolveNonrepeatableFieldUnchecked declaringGroup reference writtenGroup)).mapError .resolve
      pure (.fieldNotFilled declaration.toPresenceField)
  | .compareTextFields op leftReference rightReference => do
      let (leftPath, leftOperand, leftProfile) ←
        elaborateTextFieldOperand model declaringGroup writtenGroup leftReference
      let (rightPath, rightOperand, rightProfile) ←
        elaborateTextFieldOperand model declaringGroup writtenGroup rightReference
      finishTextFieldComparison op leftPath rightPath
        (leftOperand, leftProfile) (rightOperand, rightProfile)
  | .enumerationValueList quantifier surfaces values => do
      let operands ←
        elaborateEnumerationLiteralFieldList model declaringGroup writtenGroup surfaces values
      pure (.tokenValueList quantifier (operands.map .enumeration) (.literals values))
  | .enumerationFieldValueList quantifier fieldSurfaces valueSurfaces => do
      let (fields, values) ←
        elaborateEnumerationFieldValueSides model declaringGroup writtenGroup fieldSurfaces valueSurfaces
      pure (.tokenValueList quantifier (fields.map .enumeration)
        (.fields (values.map .enumeration)))
  | .stringValueList quantifier surfaces values => do
      let operands ←
        elaborateStringLiteralFieldList model declaringGroup writtenGroup surfaces values
      pure (.tokenValueList quantifier operands (.literals values))
  | .stringFieldValueList quantifier fieldSurfaces valueSurfaces => do
      let (fields, values) ←
        elaborateStringFieldValueSides model declaringGroup writtenGroup fieldSurfaces valueSurfaces
      pure (.tokenValueList quantifier fields (.fields values))
  | .stringValueMembership op surface values => do
      checkScalarLiteralSubjectRead model declaringGroup writtenGroup (.direct surface)
      let operand ← elaborateStringLiteralList model declaringGroup writtenGroup surface values
      pure (.tokenValueList op.quantifier [operand] (.literals values))
  | .stringFieldValueMembership op surface valueSurfaces => do
      checkScalarMemberReads model declaringGroup writtenGroup (.direct surface) (valueSurfaces.map .direct)
      let (fields, values) ←
        elaborateStringFieldValueSides model declaringGroup writtenGroup [surface] valueSurfaces
      pure (.tokenValueList op.quantifier fields (.fields values))
  | .numberValueMembership op surface values => do
      checkScalarLiteralSubjectRead model declaringGroup writtenGroup (.direct surface)
      let (operand, values) ←
        elaborateNumberLiteralMembership model declaringGroup writtenGroup surface values
      pure (.numberValueList op.quantifier [operand] (.literals values))
  | .numberFieldValueMembership op surface valueSurfaces => do
      checkScalarMemberReads model declaringGroup writtenGroup (.direct surface) (valueSurfaces.map .direct)
      let (fields, values) ←
        elaborateNumberFieldValueSides model declaringGroup writtenGroup [surface] valueSurfaces
      pure (.numberValueList op.quantifier fields (.fields values))
  | .numberFieldValueList quantifier fieldSurfaces valueSurfaces => do
      let (fields, values) ←
        elaborateNumberFieldValueSides model declaringGroup writtenGroup fieldSurfaces valueSurfaces
      pure (.numberValueList quantifier fields (.fields values))
  | .enumerationValueMembership op surface values => do
      checkScalarLiteralSubjectRead model declaringGroup writtenGroup surface
      let operand ←
        elaborateEnumerationLiteralList model declaringGroup writtenGroup surface values
      pure (.tokenValueList op.quantifier [.enumeration operand] (.literals values))
  | .enumerationFieldValueMembership op surface valueSurfaces => do
      checkScalarMemberReads model declaringGroup writtenGroup surface valueSurfaces
      let (fields, values) ←
        elaborateEnumerationFieldValueSides model declaringGroup writtenGroup [surface] valueSurfaces
      pure (.tokenValueList op.quantifier (fields.map .enumeration)
        (.fields (values.map .enumeration)))
  | .compareFields op leftReference rightReference => do
      -- Each read's gates are asked before the next read resolves, as the Kernel checks each bracket
      -- as it closes; a raw String therefore never reaches the kind match below.
      let left ← (model.resolveFieldValueRead declaringGroup leftReference writtenGroup).mapError .resolve
      let right ← (model.resolveFieldValueRead declaringGroup rightReference writtenGroup).mapError .resolve
      match left.policy.kind, right.policy.kind with
      | .temporal leftKind leftComponents, .temporal rightKind rightComponents =>
          let comparison := op.toTemporal
          if comparison.admitsFormats model.hasBaseYear leftComponents rightComponents then
            pure (.compare (.temporal comparison
              (.fieldValue { id := left.id, kind := leftKind, components := leftComponents })
              (.fieldValue { id := right.id, kind := rightKind, components := rightComponents })))
          else
            throw (.temporalFormatsIncompatible left.path right.path)
      | leftKind, rightKind =>
          match left.toTextFieldComparison?, right.toTextFieldComparison? with
          | some (leftOperand, leftProfile), some (rightOperand, rightProfile) =>
              finishTextFieldComparison op left.path right.path
                (leftOperand, leftProfile) (rightOperand, rightProfile)
          | _, _ =>
              throw (.temporalOperandKindMismatch left.path right.path
                leftKind.surfaceKind rightKind.surfaceKind)
  | .compareToday op position reference => do
      let declaration ←
        (model.resolveFieldValueRead declaringGroup reference writtenGroup).mapError .resolve
      match declaration.policy.kind with
      | .temporal kind components =>
          let comparison := op.toTemporal
          if comparison.admitsToday model.hasBaseYear components then
            let field : FlatTemporalOperand :=
              .fieldValue {
                id := declaration.id
                kind := kind
                components := components }
            let today := FlatTemporalOperand.todayValue model.timeZoneId
            pure (temporalPointComparison comparison position today field)
          else
            match position with
            | .left =>
                throw (.temporalFormatsIncompatible ["<Today>"] declaration.path)
            | .right =>
                throw (.temporalFormatsIncompatible declaration.path ["<Today>"])
      | kind =>
          match position with
          | .left =>
              throw (.temporalOperandKindMismatch ["<Today>"] declaration.path
                (.temporal .date) kind.surfaceKind)
          | .right =>
              throw (.temporalOperandKindMismatch declaration.path ["<Today>"]
                kind.surfaceKind (.temporal .date))
  | .compareBaseYear op position reference => do
      let year ← match model.baseYear with
        | some year => pure year
        | none => throw .baseYearNotDeclared
      let declaration ←
        (model.resolveFieldValueRead declaringGroup reference writtenGroup).mapError .resolve
      match declaration.policy.kind with
      | .number info =>
          let fieldOp := match position with
            | .left => op.swapped
            | .right => op
          let numeric ← match fieldOp.toNumeric? with
            | some numeric => pure numeric
            | none => throw (.unsupportedOperator op)
          if numeric.acceptsScales (.field info.scale) (.field 0) then
            pure (.compare (.number (.ordinary numeric)
              { id := declaration.id, info } year))
          else
            throw (.baseYearScaleMismatch declaration.path info.scale)
      | .temporal kind components =>
          let comparison := op.toTemporal
          if comparison.admitsBaseYear components then
            let field : FlatTemporalOperand :=
              .fieldValue {
                id := declaration.id
                kind := kind
                components := components }
            let baseYear := FlatTemporalOperand.baseYearValue model.timeZoneId year
            pure (temporalPointComparison comparison position baseYear field)
          else
            match position with
            | .left =>
                throw (.temporalFormatsIncompatible ["<BaseYear>"] declaration.path)
            | .right =>
                throw (.temporalFormatsIncompatible declaration.path ["<BaseYear>"])
      | kind =>
          match position with
          | .left =>
              throw (.temporalOperandKindMismatch ["<BaseYear>"] declaration.path
                (.temporal .date) kind.surfaceKind)
          | .right =>
              throw (.temporalOperandKindMismatch declaration.path ["<BaseYear>"]
                kind.surfaceKind (.temporal .date))
  | .compareBaseYearRange op position endpoint reference => do
      let year ← match model.baseYear with
        | some year => pure year
        | none => throw .baseYearNotDeclared
      let declaration ←
        (model.resolveFieldValueRead declaringGroup reference writtenGroup).mapError .resolve
      let sourcePath := endpoint.surfacePath
      match declaration.policy.kind with
      | .temporal kind components =>
          let comparison := op.toTemporal
          if comparison.admitsFormats true components TemporalComponents.fullDate then
            let field : FlatTemporalOperand :=
              .fieldValue {
                id := declaration.id
                kind := kind
                components := components }
            let source : FlatTemporalOperand :=
              .baseYearRangeValue model.timeZoneId year endpoint
            pure (temporalPointComparison comparison position source field)
          else
            match position with
            | .left => throw (.temporalFormatsIncompatible sourcePath declaration.path)
            | .right => throw (.temporalFormatsIncompatible declaration.path sourcePath)
      | kind =>
          match position with
          | .left =>
              throw (.temporalOperandKindMismatch sourcePath declaration.path
                (.temporal .date) kind.surfaceKind)
          | .right =>
              throw (.temporalOperandKindMismatch declaration.path sourcePath
                kind.surfaceKind (.temporal .date))
  | .compareNow op position reference => do
      let declaration ←
        (model.resolveFieldValueRead declaringGroup reference writtenGroup).mapError .resolve
      match declaration.policy.kind with
      | .temporal kind components =>
          let comparison := op.toTemporal
          if !components.hasTime then
            throw (.temporalNowRequiresTime declaration.path)
          else if !comparison.admitsNow model.hasBaseYear components then
            match position with
            | .left =>
                throw (.temporalFormatsIncompatible ["<Now>"] declaration.path)
            | .right =>
                throw (.temporalFormatsIncompatible declaration.path ["<Now>"])
          else
            let field : FlatTemporalOperand :=
              .fieldValue {
                id := declaration.id
                kind := kind
                components := components }
            pure (temporalPointComparison comparison position .nowValue field)
      | kind =>
          match position with
          | .left =>
              throw (.temporalOperandKindMismatch ["<Now>"] declaration.path
                (.temporal .dateTime) kind.surfaceKind)
          | .right =>
              throw (.temporalOperandKindMismatch declaration.path ["<Now>"]
                kind.surfaceKind (.temporal .dateTime))
  | .compareEnumeration op reference projectionRef expected => do
      let declaration ← (model.resolveProjectedFieldValueRead declaringGroup reference projectionRef
        writtenGroup).mapError .resolve
      elaborateEnumerationCore declaration op projectionRef expected
  | .compare op reference literal => do
      let declaration ← (model.resolveFieldValueRead declaringGroup reference writtenGroup).mapError .resolve
      match declaration.policy.kind with
      | .number info => do
          let numeric ← match op.toNumeric? with
            | some numeric => pure numeric
            | none => throw (.unsupportedOperator op)
          match literal with
          | .number expected =>
              pure (.compare (.number (.ordinary numeric)
                { id := declaration.id, info } expected))
          | literal =>
              throw (.literalKindMismatch declaration.path .number literal.kind)
      | .boolean => do
          let equality ← match op.toEquality? with
            | some equality => pure equality
            | none => throw (.unsupportedOperator op)
          match literal with
          | .boolean expected =>
              pure (.compare (.boolean equality { id := declaration.id } expected))
          | literal =>
              throw (.literalKindMismatch declaration.path .boolean literal.kind)
      | .confirm => do
          let equality ← match op.toEquality? with
            | some equality => pure equality
            | none => throw (.unsupportedOperator op)
          match literal with
          | .boolean expected =>
              if expected then
                pure (.compare (.confirm equality { id := declaration.id }))
              else
                throw (.illegalConfirmLiteral declaration.path)
          | literal =>
              throw (.literalKindMismatch declaration.path .confirm literal.kind)
      | .string => do
          let field ← requireStringValueField declaration
          let equality ← match op.toEquality? with
            | some equality => pure equality
            | none => throw (.unsupportedOperator op)
          match literal with
          | .string expected =>
              pure (.compare (.string equality field expected))
          | literal =>
              throw (.literalKindMismatch declaration.path .string literal.kind)
      | .enumeration =>
          match literal with
          | .string expected => elaborateEnumerationCore declaration op .stored expected
          | literal =>
              throw (.literalKindMismatch declaration.path .string literal.kind)
      | .temporal kind components =>
          match literal with
          | .date literalComponents instant =>
              let literalPath := ["<date-literal>"]
              if !literalComponents.isDateLiteral then
                throw (.invalidTemporalLiteralComponents literalPath)
              else if !literalComponents.year && !model.hasBaseYear then
                throw (.temporalLiteralNeedsBaseYear literalPath)
              else
                let comparison := op.toTemporal
                if comparison.admitsFormats model.hasBaseYear
                    components literalComponents then
                  pure (.compare (.temporal comparison
                    (.fieldValue {
                      id := declaration.id
                      kind := kind
                      components := components })
                    (.literalValue instant)))
                else
                  throw (.temporalFormatsIncompatible declaration.path literalPath)
          | literal =>
              throw (.literalKindMismatch declaration.path (.temporal kind) literal.kind)
      | .dateRange =>
          throw (.literalKindMismatch declaration.path .dateRange literal.kind)
  | .lengthCompare op reference expected => do
      let declaration ← (model.resolveEntityRead declaringGroup reference writtenGroup).mapError .resolve
      if declaration.isRawString then
        throw (.rawStringLength declaration.path)
      else
        let lengthOp ← match op.toStringLength? with
          | some lengthOp => pure lengthOp
          | none => throw (.unsupportedOperator op)
        match declaration.toStringValueField? with
        | some field =>
            pure (.compare (.stringLength lengthOp field expected.value))
        | none => throw (.lengthOperandKindMismatch declaration.path
            declaration.policy.kind.surfaceKind)
  | .literalCompareLength expected op reference => do
      let declaration ← (model.resolveEntityRead declaringGroup reference writtenGroup).mapError .resolve
      if declaration.isRawString then
        throw (.rawStringLength declaration.path)
      else
        let lengthOp ← match op.swapped.toStringLength? with
          | some lengthOp => pure lengthOp
          | none => throw (.unsupportedOperator op)
        match declaration.toStringValueField? with
        | some field =>
            pure (.compare (.stringLength lengthOp field expected.value))
        | none => throw (.lengthOperandKindMismatch declaration.path
            declaration.policy.kind.surfaceKind)
  | .and left right => do
      pure (.and (← elaborateCore model declaringGroup writtenGroup left)
        (← elaborateCore model declaringGroup writtenGroup right))
  | .or left right => do
      pure (.or (← elaborateCore model declaringGroup writtenGroup left)
        (← elaborateCore model declaringGroup writtenGroup right))

/-- Checked surface-to-core lowering. Later consumers receive the proof-bearing wrapper,
    not a caller-asserted field/policy pairing. -/
def elaborate (model : FlatModel) (declaringGroup : GroupPath)
    (condition : SurfaceCondition) (writtenGroup : GroupPath := declaringGroup) :
    Except ElabError (CheckedFlatCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let core ← elaborateCore model declaringGroup writtenGroup condition
      core.checkAgainstValidatedModel model declaringGroup hModel

end A12Kernel
