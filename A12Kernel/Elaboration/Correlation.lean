import A12Kernel.Elaboration.HavingDateValidity
import A12Kernel.Elaboration.HavingTree
import A12Kernel.Elaboration.HavingGroupPresence
import A12Kernel.Elaboration.HavingFieldValueList
import A12Kernel.Elaboration.CorrelationSurface
import A12Kernel.Elaboration.Flat.Condition.Surface
import A12Kernel.Elaboration.LiteralComparisonDiagnostic
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.StarPath
import A12Kernel.Elaboration.CorrelationWellFormed
import A12Kernel.Semantics.Correlation

/-! # A12Kernel.Elaboration.Correlation — checked lowering for repeatable filters

The established whole-rule route admits exactly one repeatable group, one starred direct-child Number field, an outer `FieldFilled` Number guard, and a correlated `Having` made from shared numeric-expression comparisons and conjunction. The general-star route also admits text literal/pair equality, Boolean/Confirm comparisons, presence and disjunction after a checked star path has fixed the complete candidate environment. Both routes accept only references available from that candidate environment or the captured rule environment and require an ordinary reference to reach a reopened level.
-/

namespace A12Kernel



/-- Whether a resolved filter uses only leaves and conjunction. This is narrower than the authored
surface, which also carries `.or`. The legacy one-group route is the only consumer, at both its
elaboration arm and its own well-formedness predicate; the star route takes the full surface. -/
def CorrelatedHaving.isConjunctive (condition : CorrelatedHaving) : Bool :=
  match condition with
  | .leaf _ => true
  | .and left right =>
      CorrelatedHaving.isConjunctive left &&
        CorrelatedHaving.isConjunctive right
  | .or _ _ => false

private def CorrelationElabError.ofSingleGroup (origin : HavingOrigin) :
    SingleGroupElabError → CorrelationElabError
  | .resolve error => .resolve error
  | .invalidGroupReference reference => .invalidGroupReference reference
  | .wildcardOnRuleGroup => .wildcardOnRuleGroup
  | .wildcardWithParentNavigation parents => .wildcardWithParentNavigation parents
  | .fieldNotNumber path actual => .fieldNotNumber path actual
  | .fieldOutsideGroup fieldPath expectedGroup =>
      .fieldOutsideGroup origin fieldPath expectedGroup
  | .fieldScopeMismatch fieldPath expected actual =>
      .fieldScopeMismatch fieldPath expected actual

/-- Class a filter body's read whose path names a group. The body's reader asks no environment as it
    resolves an unmarked reference, so such a path meets the group gate directly. -/
private def FlatModel.havingGroupRead (model : FlatModel) (declaringGroup : GroupPath)
    (reference : SurfaceFieldPath) : Unit → Option (GroupPath × Option UnboundOperandLevel) :=
  fun _ => (model.groupNamedBy? declaringGroup reference).map (·, none)

/-- The single-group route's body read with its placement requirement, that the field sit directly
    in the filtered group. The read's gates and the comparison's own classes were already asked of
    the whole body by `resolveHavingNumberRead`. -/
private def FlatModel.resolveHavingNumberInGroup (model : FlatModel)
    (declaringGroup : GroupPath) (group : RepeatableGroupDecl)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError ResolvedHavingNumberRef := do
  let (declaration, field) ← model.resolveNumberInGroup declaringGroup group reference
    |>.mapError (.ofSingleGroup origin)
  pure { declaration, core := { origin, field } }

private def resolveHavingRepetitionInGroup
    (declaringGroup : GroupPath) (group : RepeatableGroupDecl)
    (origin : HavingOrigin) (reference : SurfaceGroupReference) :
    Except CorrelationElabError HavingRepetitionRef := do
  let resolved ← reference.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup origin)
  if resolved.path != group.path then
    throw (.repetitionGroupMismatch group.path resolved.path)
  pure { origin, source := .repeatable group.level }

/-- A filter body's bracketed read on the single-group route, without the route's placement
    requirement: the read's gates, then the Number kind the leaf needs. -/
private def FlatModel.resolveHavingNumberRead (model : FlatModel) (declaringGroup : GroupPath)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError ResolvedHavingNumberRef := do
  let declaration ← (checkFieldValueRead (model.resolveFieldDeclarationUnchecked declaringGroup reference)
    (model.havingGroupRead declaringGroup reference)).mapError .resolve
  match declaration.toNumberField? with
  | some field => pure { declaration, core := { origin, field } }
  | none => throw (.fieldNotNumber declaration.path declaration.policy.kind.surfaceKind)

/-- Whether an unmarked leaf of the body reads a Number field of the filtered group. A marked
    reference reads the captured outer row, not the level the filter reopens. -/
private def SurfaceCorrelatedHaving.readsGroupNumber (model : FlatModel) (declaringGroup : GroupPath)
    (group : RepeatableGroupDecl) : SurfaceCorrelatedHaving → Bool
  | .compareFields _ left right =>
      [left, right].any fun reference => reference.origin == .inner &&
        (model.resolveNumberInGroup declaringGroup group reference.field).isOk
  | .numeric _ left right | .tolerance _ left right =>
      (left.atoms ++ right.atoms).any fun
        | .aggregate _ _ _ | .dateDifference _ _ _ | .dayDifference _ _ | .dateTimeDifference _ _ _ | .baseYear | .baseYearDatePart _ _ | .clockPart _ _ | .fieldValueAsNumber _
            | .dateRangeBoundPart _ _ _ _ | .stringLength _ _ | .stringRange _ _ _ _ | .temporalPart _ _ _ => false
        | .field reference => reference.origin == .inner &&
            (model.resolveNumberInGroup declaringGroup group reference.field).isOk
        | .repetition _ => false
  | .and left right | .or left right =>
      left.readsGroupNumber model declaringGroup group ||
        right.readsGroupNumber model declaringGroup group
  | .compareBoolean _ _ _ | .compareStrings _ _ _ | .compareTemporal _ _ _ | .fieldFill _ _ | .literalMembership _ _ _ | .fieldMembership _ _ _ | .dateValidity _ _ | .uniqueness _ | .literalList _ _ _ | .presence _ _ | .typeValidity _ _ _ | .stringPattern _ _ _ | .groupPresence _ _ _ | .groupFill _ _ _ => false

/-- Elaborate the single-group route's body in two passes. The first reads and compares the whole
    body in authored order, so each leaf's reads and comparison class answer as it closes; the
    second asks the route's placement requirement, as the star route asks its candidate environment
    only after the whole body
    ([`spec/07`](../../spec/07-repetition-and-iteration.md),
    [checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid)).
    A String leaf, which this route does not represent, still asks its read's gates first. A leaf
    outside the group draws the missing-iteration class only when no leaf reads one of the group's
    Number fields; beside such a leaf the Kernel admits it as a constant
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-predictions)). -/
private def elaborateHavingCore (model : FlatModel) (declaringGroup : GroupPath)
    (group : RepeatableGroupDecl) (authored : SurfaceCorrelatedHaving) :
    Except CorrelationElabError CorrelatedHaving := do
  discard <| elaborateHavingCoreWith {
    aggregate := fun _ _ _ => throw .stringLeafOutsideStarRoute
    baseYear := match model.baseYear with | some year => .ok year | none => .error .numericExpressionUnsupported
    clockPart := fun _ _ => throw .stringLeafOutsideStarRoute
    fieldValueAsNumber := fun _ => throw .stringLeafOutsideStarRoute
    boolean := fun _ _ _ => throw .stringLeafOutsideStarRoute
    stringValue := fun _ _ => throw .stringLeafOutsideStarRoute
    dateDifference := fun _ _ _ => throw .stringLeafOutsideStarRoute
    dayDifference := fun _ _ => throw .stringLeafOutsideStarRoute
    temporal := fun _ _ _ => throw .stringLeafOutsideStarRoute
    dateTimeDifference := fun _ _ _ => throw .stringLeafOutsideStarRoute
    dateRangeBoundPart := fun _ _ _ => throw .stringLeafOutsideStarRoute
    temporalPart := fun _ _ _ => throw .stringLeafOutsideStarRoute
    fields := fun _ _ _ => pure none
    number := model.resolveHavingNumberRead declaringGroup
    repetition := resolveHavingRepetitionInGroup declaringGroup group
    string := fun _ reference _ => do
      discard <| (checkFieldValueRead (model.resolveFieldDeclarationUnchecked declaringGroup reference.field)
        (model.havingGroupRead declaringGroup reference.field)).mapError .resolve
      throw .stringLeafOutsideStarRoute
    literalMembership := fun _ _ => throw .stringLeafOutsideStarRoute
    literalList := fun _ _ => throw .stringLeafOutsideStarRoute
    dateValidity := fun _ => throw .stringLeafOutsideStarRoute
    uniqueness := fun _ => throw .stringLeafOutsideStarRoute
    fieldMembership := fun _ _ _ => throw .stringLeafOutsideStarRoute
    fieldFill := fun _ => throw .stringLeafOutsideStarRoute
    stringPattern := fun _ _ _ => throw .stringLeafOutsideStarRoute
    typeValidity := fun _ _ _ => throw .stringLeafOutsideStarRoute
    groupPresence := fun _ _ => throw .stringLeafOutsideStarRoute
    groupFill := fun _ _ _ => throw .stringLeafOutsideStarRoute
    presence := fun _ _ => throw .stringLeafOutsideStarRoute } authored
  let readsGroup := authored.readsGroupNumber model declaringGroup group
  let condition ← (elaborateHavingCoreWith {
    aggregate := fun _ _ _ => throw .stringLeafOutsideStarRoute
    baseYear := match model.baseYear with | some year => .ok year | none => .error .numericExpressionUnsupported
    clockPart := fun _ _ => throw .stringLeafOutsideStarRoute
    fieldValueAsNumber := fun _ => throw .stringLeafOutsideStarRoute
    boolean := fun _ _ _ => throw .stringLeafOutsideStarRoute
    stringValue := fun _ _ => throw .stringLeafOutsideStarRoute
    dateDifference := fun _ _ _ => throw .stringLeafOutsideStarRoute
    dayDifference := fun _ _ => throw .stringLeafOutsideStarRoute
    temporal := fun _ _ _ => throw .stringLeafOutsideStarRoute
    dateTimeDifference := fun _ _ _ => throw .stringLeafOutsideStarRoute
    dateRangeBoundPart := fun _ _ _ => throw .stringLeafOutsideStarRoute
    temporalPart := fun _ _ _ => throw .stringLeafOutsideStarRoute
    fields := fun _ _ _ => pure none
    number := model.resolveHavingNumberInGroup declaringGroup group
    repetition := resolveHavingRepetitionInGroup declaringGroup group
    -- Preserve the legacy numeric fragment; richer leaves belong to the checked star route.
    string := fun _ _ _ => throw .stringLeafOutsideStarRoute
    literalMembership := fun _ _ => throw .stringLeafOutsideStarRoute
    literalList := fun _ _ => throw .stringLeafOutsideStarRoute
    dateValidity := fun _ => throw .stringLeafOutsideStarRoute
    uniqueness := fun _ => throw .stringLeafOutsideStarRoute
    fieldMembership := fun _ _ _ => throw .stringLeafOutsideStarRoute
    fieldFill := fun _ => throw .stringLeafOutsideStarRoute
    stringPattern := fun _ _ _ => throw .stringLeafOutsideStarRoute
    typeValidity := fun _ _ _ => throw .stringLeafOutsideStarRoute
    groupPresence := fun _ _ => throw .stringLeafOutsideStarRoute
    groupFill := fun _ _ _ => throw .stringLeafOutsideStarRoute
    presence := fun _ _ => throw .stringLeafOutsideStarRoute } authored).mapError fun
      | .fieldOutsideGroup origin fieldPath expectedGroup =>
          if readsGroup then .constantLeafBesideIteratedLeaf origin fieldPath expectedGroup
          else .fieldOutsideGroup origin fieldPath expectedGroup
      | error => error
  -- Disjunction is refused here too: this route's well-formedness predicate requires a conjunctive
  -- core, and refusing at this arm names that cause instead of failing later as an unexplained
  -- incoherence.
  if condition.isConjunctive then
    pure condition
  else
    throw .disjunctionOutsideStarRoute

/-- A marked reference's level must lie in the captured environment, asked as the reference is
    resolved. An unmarked one's candidate environment is asked only after the whole body,
    `SurfaceCorrelatedHaving.candidateEnvironmentRefusal?`. -/
private def requireOuterFieldAvailable (origin : HavingOrigin) (outerLevels : List RepeatableLevel)
    (declaration : FlatFieldDecl) : Except CorrelationElabError Unit :=
  if origin == .outer && !repeatableScopeAvailable declaration.repeatableScope outerLevels then
    throw (.fieldOutsideEnvironment origin declaration.path outerLevels declaration.repeatableScope)
  else
    pure ()

/-- A filter body's field-value read, with the gates its bracket asks as it closes. A path naming a
    group draws the group class, measured on the level the filter iterates, on a fixed group
    ([checkpoint](../../docs/sources/static-admission-and-class-probes.md#src-field-value-read-grid))
    and on a repeatable group the filter does not iterate
    ([inbound](../../docs/SOURCES.md#inbound-2026-09-25g-field-value-read)). The value gates are asked
    on the same production's account; no row reads a raw String or a partial Date in a body. A marked reference's captured
    environment is asked before the value gates and the leaf's kind gate on the assumption that it
    is the reader's class, as an unstarred repeatable level is; no row pairs it with either. -/
private def FlatModel.resolveHavingFieldValueRead (model : FlatModel) (declaringGroup : GroupPath)
    (outerLevels : List RepeatableLevel) (origin : HavingOrigin) (reference : SurfaceFieldPath)
    (projectionRef : EnumerationProjectionRef := .stored) :
    Except CorrelationElabError FlatFieldDecl := do
  let declaration ← (displaceGroupRead (model.resolveFieldDeclarationUnchecked declaringGroup reference)
    (model.havingGroupRead declaringGroup reference)).mapError .resolve
  requireOuterFieldAvailable origin outerLevels declaration
  match declaration.projectedReadRefusal? projectionRef with
  | some refusal => throw (.resolve refusal)
  | none => pure declaration

private def FlatModel.resolveHavingEntityRead (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (reference : SurfaceHavingStringRef) (valueRead : Bool := false) : Except CorrelationElabError FlatFieldDecl := do
  let declaration ← (displaceGroupRead (model.resolveFieldDeclarationUnchecked declaringGroup reference.field)
    (model.havingGroupRead declaringGroup reference.field)).mapError .resolve
  requireOuterFieldAvailable reference.origin outerLevels declaration
  (declaration.checkEntityCategoryRead (match reference.projectionRef with
    | .stored => .stored | .category category => .projected category)).mapError .fieldFill
  if valueRead then
    if let some refusal := declaration.projectedReadRefusal? reference.projectionRef then throw (.resolve refusal)
  pure declaration

private def FlatModel.resolveHavingStringPattern (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel) (compilePattern : StringPatternCompiler)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) (source : String) :
    Except CorrelationElabError (HavingPresenceRef × CompiledStringPattern) := do
  let declaration ← model.resolveHavingEntityRead declaringGroup outerLevels
    { origin, field := reference } (valueRead := true)
  if declaration.policy.kind.surfaceKind != .string then
    throw (.stringPattern (.fieldKind declaration.path declaration.policy.kind.surfaceKind))
  let pattern ← (admitStringPattern compilePattern source).mapError (CorrelationElabError.stringPattern ∘ StringPatternConditionElabError.pattern)
  pure ({ origin, field := declaration.id }, { compilePattern, pattern })

private def FlatModel.resolveHavingTypeValidity (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) (name : String) :
    Except CorrelationElabError HavingPresenceRef := do
  let declaration ← model.resolveHavingEntityRead declaringGroup outerLevels
    { origin, field := reference } (valueRead := true)
  let _ ← (elaborateCustomFieldValidityOperand model declaration.id).mapError .typeValidityOperand
  if name.isEmpty then throw (.typeValidityName .emptyTypeName)
  pure { origin, field := declaration.id }

private def FlatModel.resolveHavingLiteralMembership (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (reference : SurfaceHavingStringRef) (values : Sum (List Int) (List String)) :
    Except CorrelationElabError FlatLiteralMembership := do
  let declaration ← model.resolveHavingEntityRead declaringGroup outerLevels reference
  (elaborateLiteralMembershipCore declaration reference.projectionRef values).mapError .text

private def FlatModel.resolveHavingNumberInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError ResolvedHavingNumberRef := do
  let declaration ← model.resolveHavingFieldValueRead declaringGroup outerLevels origin reference
  let field ← match declaration.toNumberField? with
    | some field => pure field
    | none =>
        throw (.fieldNotNumber declaration.path
          declaration.policy.kind.surfaceKind)
  pure { declaration, core := { origin, field } }

/-- Resolve text in its selected environment, retaining the ordinary comparison's model-owned
    projection and literal-domain checks rather than treating a category as a stored token. -/
private def FlatModel.resolveHavingStringInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (op : EqualityOp) (reference : SurfaceHavingStringRef) (expected : String) :
    Except CorrelationElabError HavingStringRef := do
  let declaration ← model.resolveHavingFieldValueRead declaringGroup outerLevels reference.origin
    reference.field reference.projectionRef
  let operand ← match declaration.policy.kind with
    | .enumeration => do
        let surfaceOp := match op with | .equal => SurfaceComparisonOp.equal | .notEqual => .notEqual
        let .compare (.enumeration _ operand _) ←
          (elaborateEnumerationCore declaration surfaceOp reference.projectionRef expected).mapError .text
          | throw .incoherentCore
        pure (.enumeration operand)
    | _ =>
        match declaration.toStringValueField?, reference.projectionRef with
        | some field, .stored => pure (.string field)
        | _, _ => throw (.fieldNotStringValue declaration.path declaration.policy.kind.surfaceKind)
  pure { origin := reference.origin, operand }

private def havingTextOperand (declaration : FlatFieldDecl)
    (projectionRef : EnumerationProjectionRef) :
    Except CorrelationElabError (FlatTextFieldOperand × DirectComparableField) := do
  match projectionRef with
  | .stored =>
      match declaration.toTextFieldComparison? with
      | some operand => pure operand
      | none => throw (.text (.textFieldOperandKindMismatch declaration.path declaration.policy.kind.surfaceKind))
  | .category _ =>
      match declaration.toEnumerationTextFieldComparison? projectionRef with
      | some operand => pure operand
      | none => throw .incoherentCore

private def FlatModel.resolveHavingFieldsInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (op : SurfaceComparisonOp) (left right : SurfaceHavingStringRef) :
    Except CorrelationElabError (Option FlatComparison) := do
  let numberSide := [left, right].any fun reference =>
    (model.resolveFieldDeclarationUnchecked declaringGroup reference.field).toOption.any fun declaration =>
      declaration.policy.kind.surfaceKind == .number
  if numberSide && left.projectionRef == .stored && right.projectionRef == .stored then
    pure none
  else
    let leftDecl ← model.resolveHavingFieldValueRead declaringGroup outerLevels left.origin left.field left.projectionRef
    let rightDecl ← model.resolveHavingFieldValueRead declaringGroup outerLevels right.origin right.field right.projectionRef
    if left.projectionRef == .stored && right.projectionRef == .stored then
      match leftDecl.policy.kind, rightDecl.policy.kind with
      | .temporal _ _, .temporal _ _ =>
          return some (← (elaborateTemporalFieldPair model.hasBaseYear op.toTemporal leftDecl rightDecl).mapError .text)
      | _, _ => pure ()
    let some equality := op.toEquality? |
      throw (.orderingFieldNotNumber leftDecl.path leftDecl.policy.kind.surfaceKind rightDecl.policy.kind.surfaceKind)
    if left.projectionRef == .stored && right.projectionRef == .stored then
      match leftDecl.policy.kind, rightDecl.policy.kind with
      | .dateRange, .dateRange =>
          let some leftProfile := (certifyDateRangeInputField leftDecl).toOption | throw .incoherentCore
          let some rightProfile := (certifyDateRangeInputField rightDecl).toOption | throw .incoherentCore
          if leftProfile.format.components != rightProfile.format.components then
            throw (.dateRangeComponentsMismatch leftDecl.path rightDecl.path)
          return some (.dateRange equality { id := leftDecl.id } { id := rightDecl.id })
      | .boolean, .boolean => return some (.booleanFields equality
          (.boolean { id := leftDecl.id }) (.boolean { id := rightDecl.id }))
      | .confirm, .confirm =>
          if equality == .equal then throw (.text (.illegalConfirmLiteral leftDecl.path))
          return some (.booleanFields equality
            (.confirm { id := leftDecl.id }) (.confirm { id := rightDecl.id }))
      | _, _ => pure ()
    let leftOperand ← havingTextOperand leftDecl left.projectionRef
    let rightOperand ← havingTextOperand rightDecl right.projectionRef
    match classifyDirectFieldComparison leftOperand.2 rightOperand.2 with
    | .accepted => pure (some (.textFields equality leftOperand.1 rightOperand.1))
    | .rejected error => throw (.text (.enumerationComparability leftDecl.path rightDecl.path error))

private def FlatModel.resolveHavingTemporalOperand (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel) :
    SurfaceHavingTemporalOperand → Except CorrelationElabError (HavingOrigin × FlatTemporalOperand)
  | .field reference => do
      let declaration ← model.resolveHavingFieldValueRead declaringGroup outerLevels
        reference.origin reference.field reference.projectionRef
      if reference.projectionRef != .stored then throw .incoherentCore
      let some field := declaration.toTemporalField? | throw .numericExpressionUnsupported
      pure (reference.origin, .fieldValue field)
  | .grouped source => do
      let (origin, operand) ← model.resolveHavingTemporalOperand declaringGroup outerLevels source
      pure (origin, .grouped operand)
  | .timeLiteral value => pure (.inner, .timeValue value)
  | .dateTimeLiteral value => do
      let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .numericExpressionUnsupported
      pure (.inner, .localDateTimeValue profile value)
  | .constant source => do
      let operand ← match source with
        | .field impossible => nomatch impossible
        | .today => pure (.todayValue model.timeZoneId)
        | .now => pure .nowValue
        | .baseYear source => do
            let some year := model.baseYear | throw (.text .baseYearNotDeclared)
            pure (match source with
              | .direct => .baseYearValue model.timeZoneId year
              | .range endpoint => .baseYearRangeValue model.timeZoneId year endpoint)
        | .literal literal => do
            let some instant := literal.comparisonInstant? model | throw .numericExpressionUnsupported
            pure (.literalValue instant literal.components)
      pure (.inner, operand)

private def FlatModel.resolveHavingTemporalConstant (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (op : SurfaceComparisonOp) (left right : SurfaceHavingTemporalOperand) :
    Except CorrelationElabError (Option (HavingOrigin × HavingOrigin × FlatComparison)) := do
  let rec numeric : SurfaceHavingTemporalOperand → Except CorrelationElabError Bool
    | .field reference => do
        let declaration ← model.resolveHavingFieldValueRead declaringGroup outerLevels
          reference.origin reference.field reference.projectionRef
        pure (reference.projectionRef == .stored && declaration.policy.kind.surfaceKind == .number)
    | .constant (.baseYear .direct) => pure true
    | .grouped source => numeric source
    | _ => pure false
  if (← numeric left) && (← numeric right) then return none
  let (leftOrigin, left) ← model.resolveHavingTemporalOperand declaringGroup outerLevels left
  let (rightOrigin, right) ← model.resolveHavingTemporalOperand declaringGroup outerLevels right
  if !comparisonConstantPairAllowed left.havingEntry right.havingEntry then throw .constantNumericComparison
  if !model.admitsHavingTemporalOperands op.toTemporal left right then throw .numericExpressionUnsupported
  pure (some (leftOrigin, rightOrigin, .temporal op.toTemporal left right))

private def FlatModel.resolveHavingBooleanInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (op : EqualityOp) (reference : SurfaceHavingStringRef) (expected : Bool) :
    Except CorrelationElabError FlatComparison := do
  let declaration ← model.resolveHavingFieldValueRead declaringGroup outerLevels
    reference.origin reference.field reference.projectionRef
  if reference.projectionRef != .stored then throw .incoherentCore
  match declaration.policy.kind with
  | .boolean => pure (.boolean op { id := declaration.id } expected)
  | .confirm =>
      if expected then pure (.confirm op { id := declaration.id })
      else throw (.text (.illegalConfirmLiteral declaration.path))
  | kind => throw (.text (.literalKindMismatch declaration.path .boolean kind.surfaceKind))

/-- Resolve one presence filter reference. Presence accepts any declared field, so this checks the
    declaration's existence and a marked one's captured environment, with no kind gate. -/
private def FlatModel.resolveHavingPresenceInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (origin : HavingOrigin) (reference : SurfaceFieldPath) :
    Except CorrelationElabError HavingPresenceRef := do
  let declaration ←
    (model.resolveFieldDeclarationUnchecked declaringGroup reference).mapError .resolve
  requireOuterFieldAvailable origin outerLevels declaration
  pure { origin, field := declaration.id }

private def FlatModel.resolveHavingRepetitionInEnvironment (model : FlatModel)
    (declaringGroup : GroupPath) (outerLevels : List RepeatableLevel)
    (origin : HavingOrigin) (reference : SurfaceGroupReference) :
    Except CorrelationElabError HavingRepetitionRef := do
  let resolved ← reference.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup origin)
  if !model.hasGroupPath resolved.path then
    throw (.unknownRepetitionGroup resolved.path)
  if origin == .outer then
    let scope := model.repeatableScopeForGroupPath resolved.path
    if let some missing := scope.find? fun level => !outerLevels.contains level then
      throw (.repetitionOutsideEnvironment origin resolved.path outerLevels missing)
  let source := match model.repeatableGroups.find? (fun group => group.path == resolved.path) with
    | some group => HavingRepetitionSource.repeatable group.level
    | none => .fixed resolved.path
  pure { origin, source }

/-- An outer filter reference contributes its declaration's scope whatever the reference's kind, so
    this reads the origin and the field id rather than a kind-specific reference type. -/
private def outerHavingFieldIterationScope
    (model : FlatModel) (origin : HavingOrigin) (fieldId : FieldId) :
    Option (List RepeatableLevel) :=
  match origin with
  | .inner => none
  | .outer =>
      match model.lookupUniqueId fieldId with
      | .error _ => none
      | .ok declaration =>
          if declaration.repeatableScope.isEmpty then
            none
          else
            some declaration.repeatableScope

private def outerHavingNumberIterationScope
    (model : FlatModel) (reference : HavingNumberRef) :
    Option (List RepeatableLevel) :=
  outerHavingFieldIterationScope model reference.origin reference.field.id

private def outerHavingRepetitionIterationScope
    (model : FlatModel)
    (reference : HavingRepetitionRef) :
    Option (List RepeatableLevel) :=
  match reference.origin with
  | .inner => none
  | .outer => (reference.scope? model).bind fun scope =>
      if scope.isEmpty then none else some scope

def CorrelatedHaving.outerIterationScopes
    (model : FlatModel) :
    CorrelatedHaving → List (Option (List RepeatableLevel))
  | .leaf (.numeric comparison) =>
      (comparison.left.atoms ++ comparison.right.atoms).flatMap fun
        | .aggregate _ first rest => (first :: rest).map (outerHavingNumberIterationScope model)
        | .dateDifference _ left right | .dayDifference _ left right => (left.fields ++ right.fields).map fun reference =>
            outerHavingFieldIterationScope model reference.origin reference.field.id
        | .dateTimeDifference _ left right => (left.fieldValues ++ right.fieldValues).map fun reference =>
            outerHavingFieldIterationScope model reference.origin reference.field.id
        | .baseYear _ | .baseYearDatePart _ _ _ | .clockPart _ _ _ => [none]
        | .fieldValueAsNumber origin source => [outerHavingFieldIterationScope model origin source.fieldId]
        | .field reference => [outerHavingNumberIterationScope model reference]
        | .stringLength origin field | .stringRange origin field _ _ => [outerHavingFieldIterationScope model origin field.id]
        | .dateRangeBoundPart origin field _ _ => [outerHavingFieldIterationScope model origin field.id]
        | .temporalPart origin field _ => [outerHavingFieldIterationScope model origin field.id]
        | .repetition reference => [outerHavingRepetitionIterationScope model reference]
  | .leaf (.simpleComparison left right comparison) =>
      comparison.inputFields.1.map (fun field => outerHavingFieldIterationScope model left field.id) ++
        comparison.inputFields.2.map (fun field => outerHavingFieldIterationScope model right field.id)
  | .leaf (.compareStringLiteral _ reference _) =>
      [outerHavingFieldIterationScope model reference.origin reference.field.id]
  | .leaf (.literalMembership origin _ source) =>
      [outerHavingFieldIterationScope model origin source.field.id]
  | .leaf (.dateValidity _ source) =>
      source.references.map fun ref => outerHavingFieldIterationScope model ref.origin ref.field
  | .leaf (.uniqueness source) =>
      source.presenceSlots.map fun slot => do
        let reference ← slot.references.head?
        if reference.origin != .outer then none
        let scope ← slot.bindingScope? model
        if scope.isEmpty then none else some scope
  | .leaf (.fieldMembership _ source) =>
      source.references.map fun ref => outerHavingFieldIterationScope model ref.origin ref.field
  | .leaf (.fieldFill _ references) =>
      references.map fun ref => outerHavingFieldIterationScope model ref.origin ref.field
  | .leaf (.presence _ reference) | .leaf (.typeValidity _ reference _) | .leaf (.stringPattern _ reference _) =>
      [outerHavingFieldIterationScope model reference.origin reference.field]
  | .leaf (.groupPresence _ origin source) =>
      [if origin == .outer && !source.content.scope.isEmpty then some source.content.scope else none]
  | .leaf (.groupFill _ first rest) => (first :: rest).map fun
      | .field reference => outerHavingFieldIterationScope model reference.origin reference.field
      | .group origin source =>
          if origin == .outer && !source.content.scope.isEmpty then some source.content.scope else none
  | .and left right | .or left right =>
      CorrelatedHaving.outerIterationScopes model left ++
        CorrelatedHaving.outerIterationScopes model right

/-- One filter certified against the candidate path and captured binding group. Lexical resolution
uses the separate declaring group passed to `elaborateStarHavingCore`. -/
structure CheckedStarHaving (model : FlatModel)
    (source : CheckedStarFieldPath model) (bindingGroup : GroupPath) where
  authored : CorrelatedHaving
  wellFormed : authored.wellFormedForEnvironments model
    (source.path.axes.map (·.level))
    (model.repeatableScopeForGroupPath bindingGroup) = true
  reachesReopenedLevel : authored.reachesReopenedLevel model
    ((source.path.axes.map (·.level)).drop source.path.firstStar) = true

def CheckedStarHaving.condition
    (checked : CheckedStarHaving model source declaringGroup) :
    CorrelatedHaving :=
  checked.authored

/-- The first **unmarked** reference of an authored filter, in authored order, whose level its
    candidate environment does not hold. The star route asks it once every leaf has resolved and
    passed its comparison's kind and scale gates, because the Kernel names a body's refused
    comparison ahead of the filter's iteration class, on a repetition the filter does not iterate
    too ([inbound](../../docs/SOURCES.md#inbound-2026-09-25c-filter-body)). -/
def SurfaceCorrelatedHaving.candidateEnvironmentRefusal? (model : FlatModel)
    (declaringGroup : GroupPath) (candidateLevels : List RepeatableLevel) :
    SurfaceCorrelatedHaving → Option CorrelationElabError
  | .numeric _ left right | .tolerance _ left right =>
      (left.atoms ++ right.atoms).findSome? fun
        | .aggregate _ first rest => (first :: rest).findSome? fun reference => field reference.origin reference.field
        | .dateDifference _ left right | .dayDifference left right =>
            (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
        | .dateTimeDifference _ left right =>
            (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
        | .baseYear | .baseYearDatePart _ _ | .clockPart _ _ => none
        | .fieldValueAsNumber reference => field reference.origin reference.field
        | .field reference => field reference.origin reference.field
        | .dateRangeBoundPart origin reference _ _ | .stringLength origin reference | .stringRange origin reference _ _ | .temporalPart origin reference _ => field origin reference
        | .repetition reference => group reference.origin reference.group
  | .compareFields _ left right =>
      (field left.origin left.field).orElse fun _ => field right.origin right.field
  | .compareBoolean _ reference _ | .compareStrings _ reference _ => field reference.origin reference.field
  | .compareTemporal _ left right =>
      (left.fields ++ right.fields).findSome? fun reference => field reference.origin reference.field
  | .literalMembership _ reference _ => field reference.origin reference.field
  | .fieldMembership _ subjects members =>
      (subjects.first :: subjects.rest ++ members.first :: members.rest).findSome? fun ref => field ref.origin ref.field
  | .dateValidity _ source => source.references.findSome? fun ref => field ref.origin ref.field
  | .uniqueness source => (source.first :: source.rest).findSome? fun ref => do
      guard (ref.origin == .inner)
      let (path, scope) ← ref.bindingRead? model declaringGroup
      guard !(repeatableScopeAvailable scope candidateLevels)
      pure (.fieldOutsideEnvironment .inner path candidateLevels scope)
  | .literalList _ source _ | .fieldFill _ source => (source.first :: source.rest).findSome? fun ref => field ref.origin ref.field
  | .presence _ reference | .typeValidity _ reference _ | .stringPattern _ reference _ => field reference.origin reference.field
  | .groupPresence _ origin reference => group origin reference
  | .groupFill _ first rest => (first :: rest).findSome? fun (origin, reference) => group origin reference
  | .and left right | .or left right =>
      (left.candidateEnvironmentRefusal? model declaringGroup candidateLevels).orElse fun _ =>
        right.candidateEnvironmentRefusal? model declaringGroup candidateLevels
where
  field (origin : HavingOrigin) (reference : SurfaceFieldPath) : Option CorrelationElabError := do
    guard (origin == .inner)
    let declaration ← (model.resolveFieldDeclarationUnchecked declaringGroup reference).toOption
    guard !(repeatableScopeAvailable declaration.repeatableScope candidateLevels)
    pure (.fieldOutsideEnvironment .inner declaration.path candidateLevels
      declaration.repeatableScope)
  group (origin : HavingOrigin) (reference : SurfaceGroupReference) :
      Option CorrelationElabError := do
    guard (origin == .inner)
    let resolved ← (reference.resolveAgainst declaringGroup).toOption
    let missing ← (model.repeatableScopeForGroupPath resolved.path).find? fun level =>
      !candidateLevels.contains level
    pure (.repetitionOutsideEnvironment .inner resolved.path candidateLevels missing)

/-- Lower the supported filter tree against one validated star plan. The result retains the authored connectives and exact candidate/captured environment split established by the checked references. -/
def elaborateStarHavingCore (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (authored : SurfaceCorrelatedHaving)
    (bindingGroup : GroupPath := declaringGroup)
    (compilePattern : StringPatternCompiler := locallyExecutableStringPatternMatcher?) :
    Except CorrelationElabError (CheckedStarHaving model source bindingGroup) := do
  let candidateLevels := source.path.axes.map (·.level)
  let reopenedLevels := candidateLevels.drop source.path.firstStar
  let outerLevels := model.repeatableScopeForGroupPath bindingGroup
  let resolveTemporal (admitted : TemporalComponents → Bool)
      (reference : SurfaceHavingTemporalRef) : Except CorrelationElabError HavingTemporalRef := do
    let declaration ← model.resolveHavingEntityRead declaringGroup outerLevels { origin := reference.origin, field := reference.field }
    let some source := declaration.toTemporalField? | throw .numericExpressionUnsupported
    if !admitted source.components then throw .numericExpressionUnsupported
    pure { origin := reference.origin, field := source }
  let resolveCalendar (admitted : TemporalComponents → Bool) :
      SurfaceDateDifferenceOperand SurfaceHavingTemporalRef → Except CorrelationElabError (ResolvedDateDifferenceOperand HavingTemporalRef)
    | .literal source => if source.valid then pure (.literal source model.baseYearOrDefault) else throw .numericExpressionUnsupported
    | .field reference => .field <$> resolveTemporal admitted reference
    | .baseYear source => match model.baseYear with
        | some year => pure (.baseYear year source)
        | none => throw .numericExpressionUnsupported
    | .today => match ModelZone.ConcreteProfile.ofId? model.timeZoneId with
        | some profile => pure (.today profile)
        | none => throw .numericExpressionUnsupported
    | .now => throw .numericExpressionUnsupported
  let condition ← elaborateHavingCoreWith {
    aggregate := fun op first rest => do
      if rest.isEmpty then throw .numericExpressionUnsupported
      let resolve (reference : SurfaceHavingNumberRef) :=
        (model.resolveHavingNumberInEnvironment declaringGroup outerLevels reference.origin reference.field).map (·.core)
      let first ← resolve first
      let rest ← rest.mapM resolve
      if !havingAggregateUnique first rest then throw .numericExpressionUnsupported
      pure (.aggregate op first rest)
    baseYear := match model.baseYear with | some year => .ok year | none => .error .numericExpressionUnsupported
    clockPart := fun source part => do
      if !source.admits part then throw .numericExpressionUnsupported
      let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .numericExpressionUnsupported
      pure (.clockPart source profile part)
    fieldValueAsNumber := fun reference => do
      let declaration ← model.resolveHavingEntityRead declaringGroup outerLevels reference
      (declaration.resolveFieldValueAsNumberSource reference.projectionRef).mapError (fun _ => .numericExpressionUnsupported)
    boolean := model.resolveHavingBooleanInEnvironment declaringGroup outerLevels
    stringValue := fun origin reference => do
      let declaration ← model.resolveHavingFieldValueRead declaringGroup outerLevels origin reference .stored
      match declaration.toStringValueField? with
      | some field => pure field
      | none => throw (.text (.lengthOperandKindMismatch declaration.path declaration.policy.kind.surfaceKind))
    dateDifference := fun unit left right => do
      let resolve := resolveCalendar (unit.admittedBy model.hasBaseYear)
      let first ← resolve left
      let second ← resolve right
      if !unit.compatible model.hasBaseYear (first.componentsWith (·.field.components)) (second.componentsWith (·.field.components)) then throw .numericExpressionUnsupported
      pure (.dateDifference unit first second)
    dayDifference := fun left right => do
      let resolve := resolveCalendar (CalendarDayDifference.admittedBy)
      let first ← resolve left
      let second ← resolve right
      if !CalendarDayDifference.admittedBy (first.componentsWith (·.field.components)) ||
          !CalendarDayDifference.admittedBy (second.componentsWith (·.field.components)) ||
          !CalendarDayDifference.yearCompatible model.hasBaseYear (first.componentsWith (·.field.components)) (second.componentsWith (·.field.components)) then throw .numericExpressionUnsupported
      let some profile := ModelZone.ConcreteProfile.ofId? model.timeZoneId | throw .numericExpressionUnsupported
      pure (.dayDifference profile first second)
    dateTimeDifference := fun unit left right => do
      let resolve : SurfaceDateDifferenceOperand SurfaceHavingTemporalRef →
          Except CorrelationElabError (FlatTemporalOperand HavingTemporalRef)
        | .field reference => .fieldValue <$> resolveTemporal unit.admittedBy reference
        | .now => pure .nowValue
        | _ => throw .numericExpressionUnsupported
      let first ← resolve left
      let second ← resolve right
      let some firstComponents := first.dateTimeDifferenceComponentsWith? (·.field.components) | throw .numericExpressionUnsupported
      let some secondComponents := second.dateTimeDifferenceComponentsWith? (·.field.components) | throw .numericExpressionUnsupported
      if !unit.compatible firstComponents secondComponents then throw .numericExpressionUnsupported
      pure (.dateTimeDifference unit first second)
    dateRangeBoundPart := fun origin reference part => do
      let declaration ← model.resolveHavingEntityRead declaringGroup outerLevels { origin, field := reference }
      let source : FlatDateRangeField := { id := declaration.id }
      if !model.exposesDateRangeBoundPart source part then throw .numericExpressionUnsupported
      pure source
    temporalPart := fun origin reference part => do
      let declaration ← model.resolveHavingEntityRead declaringGroup outerLevels { origin, field := reference }
      let some source := declaration.toTemporalField? | throw .numericExpressionUnsupported
      if !part.admittedBy source model.hasBaseYear then throw .numericExpressionUnsupported
      pure source
    temporal := model.resolveHavingTemporalConstant declaringGroup outerLevels
    fields := model.resolveHavingFieldsInEnvironment declaringGroup outerLevels
    number := model.resolveHavingNumberInEnvironment declaringGroup outerLevels
    repetition := model.resolveHavingRepetitionInEnvironment declaringGroup outerLevels
    string := model.resolveHavingStringInEnvironment declaringGroup outerLevels
    literalMembership := model.resolveHavingLiteralMembership declaringGroup outerLevels
    literalList := fun subjects values =>
      elaborateHavingTokenLiteralList model subjects values (fun ref =>
        model.resolveHavingEntityRead declaringGroup outerLevels {
          origin := ref.origin, field := ref.field, projectionRef := match ref.form with
            | .stored => .stored | .projected category => .category category })
    dateValidity := elaborateHavingDateComponents model (fun ref =>
      model.resolveHavingEntityRead declaringGroup outerLevels { origin := ref.origin, field := ref.field })
    uniqueness := elaborateHavingUniqueness model declaringGroup candidateLevels outerLevels
    fieldMembership := fun operator subjects members =>
      let read (valueRead : Bool) (ref : SurfaceHavingDirectFieldOperand) :=
        model.resolveHavingEntityRead declaringGroup outerLevels {
          origin := ref.origin, field := ref.field, projectionRef := match ref.form with
            | .stored => .stored | .projected category => .category category } valueRead
      elaborateHavingFieldValueList (model := model) operator subjects members (read false) (read true)
    fieldFill := fun source => do
      let checked ← elaborateHavingDirectFieldSource model declaringGroup candidateLevels outerLevels source .deferCandidate
        |>.mapError .fieldFill
      checked.operands.mapM fun operand => do
        if operand.form != .stored then throw .incoherentCore
        pure { origin := operand.origin, field := operand.declaration.id }
    stringPattern := model.resolveHavingStringPattern declaringGroup outerLevels compilePattern
    typeValidity := model.resolveHavingTypeValidity declaringGroup outerLevels
    groupPresence := model.resolveHavingGroupPresence declaringGroup outerLevels
    groupFill := model.resolveHavingGroupFill declaringGroup outerLevels
    presence := model.resolveHavingPresenceInEnvironment declaringGroup outerLevels } authored
  if let some refusal := authored.candidateEnvironmentRefusal? model declaringGroup candidateLevels then
    throw refusal
  if hReopened : condition.reachesReopenedLevel model reopenedLevels = true then
    if hWellFormed :
        condition.wellFormedForEnvironments model candidateLevels outerLevels = true then
      pure {
        authored := condition
        wellFormed := hWellFormed
        reachesReopenedLevel := hReopened }
    else
      throw .incoherentCore
  else
    throw .missingInner

namespace CheckedStarFieldPath

/-- Apply one checked validation `Having` to topology-produced leaves before invoking the kind-specific cell classifier. Every filtered star consumer shares this order and the retained filter marker. -/
def selectedValidationHavingValueListSide (_checked : CheckedStarFieldPath model)
    (resolved : ResolvedStarTopology) (having : CorrelatedHaving)
    (filterRead : Env → FieldId → CheckedCell) (outer : Env)
    (classify : Env → ValueListCell kind)
    (world : Option World := none) : ResolvedValueListSide kind :=
  let filterContext : CorrelationContext := { read := filterRead, world }
  let selected := having.selectEnvironments filterContext outer resolved.environments
  { cells := selected.map classify
    hasUninstantiatedTail := resolved.domain.hasOpenTail
    hasHaving := true }

/-- Resolve nested topology once, filter every candidate against its complete candidate/captured environments, and classify only retained leaves. -/
def resolvedValidationHavingValueListSide (checked : CheckedStarFieldPath model)
    (document : Document) (outer : Env) (having : CorrelatedHaving)
    (filterRead : Env → FieldId → CheckedCell)
    (classify : Env → ValueListCell kind)
    (world : Option World := none) :
    Except StarAddressingError (ResolvedValueListSide kind) := do
  let resolved ← checked.path.resolveInCapacity document outer
  pure (checked.selectedValidationHavingValueListSide resolved having filterRead outer classify world)

/-- Dispatch one optional checked validation filter without duplicating the filter-before-classification branch in each scalar-kind adapter. -/
def resolvedOptionalValidationHavingValueListSide
    (checked : CheckedStarFieldPath model) (document : Document) (outer : Env)
    (filter : Option (CheckedStarHaving model checked declaringGroup))
    (filterRead : Env → FieldId → CheckedCell)
    (classify : Env → ValueListCell kind)
    (world : Option World := none) :
    Except StarAddressingError (ResolvedValueListSide kind) :=
  match filter with
  | none => checked.resolvedValueListSide document outer classify
  | some having =>
      checked.resolvedValidationHavingValueListSide document outer
        having.condition filterRead classify world

end CheckedStarFieldPath

/-- Partial validation skips a complete rule containing `Having` before topology or operand reads; otherwise it returns the evaluated value-list verdict. -/
inductive PartialHavingValueListResult where
  | skippedHaving
  | evaluated (verdict : Verdict)
  deriving Repr, DecidableEq

structure ResolvedSingleCorrelatedRule where
  group : RepeatableGroupDecl
  errorField : FlatNumberField
  guardField : FlatNumberField
  star : SingleCorrelatedStar

def ResolvedSingleCorrelatedRule.wellFormedBool
    (rule : ResolvedSingleCorrelatedRule) (model : FlatModel) : Bool :=
  model.repeatableGroups.contains rule.group &&
    model.admitsSingleGroupNumber rule.group rule.errorField &&
    model.admitsSingleGroupNumber rule.group rule.guardField &&
    rule.errorField == rule.guardField &&
    model.admitsSingleGroupNumber rule.group rule.star.valueField &&
    rule.star.having.condition.isConjunctive &&
    rule.star.having.condition.wellFormedForSingleGroup model rule.group

def ResolvedSingleCorrelatedRule.WellFormed
    (rule : ResolvedSingleCorrelatedRule) (model : FlatModel) : Prop :=
  rule.wellFormedBool model = true

/-- The only repeatable surface-to-core result accepted by the checked runtime route. -/
structure CheckedSingleCorrelatedRule (model : FlatModel) where
  core : ResolvedSingleCorrelatedRule
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.WellFormed model

/-- Checked lowering for the exact one-star correlated validation fragment. All-inner `Having` is rejected as a routing boundary to the earlier uncorrelated capsule; it is not classified as kernel-invalid here. -/
def elaborateSingleCorrelatedRule (model : FlatModel) (declaringGroup : GroupPath)
    (rule : SurfaceSingleCorrelatedRule) :
    Except CorrelationElabError (CheckedSingleCorrelatedRule model) :=
  match hModel : model.validate with
  | .error error => .error (.resolve error)
  | .ok () => do
      let groupReference ← rule.valueField.groupReference |>.mapError (.ofSingleGroup .inner)
      let groupPath ← groupReference.resolveAgainst declaringGroup |>.mapError (.ofSingleGroup .inner)
      let group ← (model.lookupUniqueRepeatablePath groupPath).mapError .resolve
      let valueReference : SurfaceFieldPath :=
        { base := .absolute, groups := group.path, field := rule.valueField.field }
      let (_, valueField) ←
        model.resolveNumberInGroup declaringGroup group valueReference |>.mapError (.ofSingleGroup .inner)
      let (errorDeclaration, errorField) ←
        model.resolveNumberInGroup declaringGroup group rule.errorField |>.mapError (.ofSingleGroup .inner)
      let (guardDeclaration, guardField) ←
        model.resolveNumberInGroup declaringGroup group rule.guardField |>.mapError (.ofSingleGroup .inner)
      if errorField != guardField then
        throw (.errorGuardMismatch errorDeclaration.path guardDeclaration.path)
      let condition ← elaborateHavingCore model declaringGroup group rule.having
      let having ← match condition.check with
        | .ok checked => pure checked
        | .error .missingInner => throw .missingInner
        | .error .missingOuter => throw .missingOuter
      let core : ResolvedSingleCorrelatedRule :=
        { group, errorField, guardField, star := { valueField, having } }
      if hCore : core.wellFormedBool model = true then
        pure {
          core
          modelWellFormed := by
            rw [hModel]
            rfl
          wellFormed := hCore
        }
      else
        throw .incoherentCore

def CheckedSingleCorrelatedRule.firingRows
    (checked : CheckedSingleCorrelatedRule model) (raw : RawSingleGroupContext) :
    Except SingleGroupContextError (List RowIndex) := do
  raw.validate
  pure <| checked.core.star.firingRowsOn checked.core.guardField
    (model.checkSingleGroupContext checked.core.group raw)

end A12Kernel
