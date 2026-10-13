import A12Kernel.Reference.Dm.HavingListAdmission
import A12Kernel.Reference.Dm.HavingOperationShape
import A12Kernel.Reference.Dm.FilterReferenceInventory
import A12Kernel.Elaboration.NumericComputation.OperationTyping
import A12Kernel.Elaboration.TableEnumeration

namespace A12Kernel.Dm
open HavingListAdmission

mutual
/-- Traverse authored references, including keys, scopes and range endpoints, without resolving
or lowering them. Admission activation must not itself reorder read failures (spec/07 §3). -/
private partial def Expr.anyReference (test : Reference → Bool) (callTest : String → Bool := fun _ => false) : Expr → Bool
  | .entity reference | .value reference => reference.anyReference test callTest
  | .arith _ left right | .compare _ left right => left.anyReference test callTest || right.anyReference test callTest
  | .braces body | .parens body => body.anyReference test callTest
  | .logic _ parts => parts.any (Expr.anyReference test callTest)
  | .call name arguments listed scope =>
      callTest name ||
      arguments.any (Argument.anyReference test callTest) || (listed.getD []).any (Argument.anyReference test callTest) ||
        scope.any (Reference.anyReference test callTest)
  | _ => false

private partial def Reference.anyReference (test : Reference → Bool) (callTest : String → Bool := fun _ => false) (reference : Reference) : Bool :=
  test reference || reference.filter.any (Expr.anyReference test callTest) || match reference.index with
    | some (.reference key) => key.anyReference test callTest
    | _ => false

private partial def Argument.anyReference (test : Reference → Bool) (callTest : String → Bool := fun _ => false) : Argument → Bool
  | .mk expression rangeEnd => expression.anyReference test callTest || rangeEnd.any (Expr.anyReference test callTest)
end

/-- Activate ordered admission across an entire filter-containing expression, including its
preceding operands and separate lists (spec/07 §3). -/
def Expr.hasHaving : Expr → Bool := Expr.anyReference (·.filter.isSome)
def Reference.hasHaving : Reference → Bool := Reference.anyReference (·.filter.isSome)
def Argument.hasHaving : Argument → Bool := Argument.anyReference (·.filter.isSome)

/-- An operation call (`Abs`, `Min`, `Max`, a rounding or a numeric field form) one of whose
operands is a comparison or a connective, which the grammar does not admit there. -/
private partial def Expr.hasConditionAsOperationOperand : Expr → Bool
  | .call id arguments listed _ =>
      let operation := id == "Abs" || id == "Min" || id == "Max" ||
        (roundingMode? id).isSome || isNumericFieldForm id
      let condition : Expr → Bool
        | .compare .. | .logic .. => true
        | _ => false
      let nested (argument : Argument) : Bool := match argument with
        | .mk operand rangeEnd => operand.hasConditionAsOperationOperand ||
            (rangeEnd.map (·.hasConditionAsOperationOperand)).getD false
      let operandIsCondition (argument : Argument) : Bool := match argument with
        | .mk operand _ => condition operand
      (operation && arguments.any operandIsCondition) || arguments.any nested || (listed.getD []).any nested
  | .compare _ left right | .arith _ left right =>
      left.hasConditionAsOperationOperand || right.hasConditionAsOperationOperand
  | .logic _ parts => parts.any (·.hasConditionAsOperationOperand)
  | .braces body | .parens body => body.hasConditionAsOperationOperand
  | _ => false

/-- Authored scalar slots, lists and repetition operands need their parse/read diagnostics before
lowering loses their shape (spec/07 §5–6, spec/08 CurrentRepetition cascade; KF532). -/
def Expr.needsOrderedAdmission (expression : Expr) : Bool :=
  expression.hasHaving || expression.hasConditionAsOperationOperand || expression.anyReference (fun _ => false)
    (fun name => name == "Date" || name == "Time" || name == "CurrentRepetition" ||
      name == "RepetitionNotUnique" || name == "FirstFilledValue" ||
      (rawScalarOperator? name).isSome)

/-- Retain projected target identity across all authored fragments before alternative lowering
(spec/09 §6, self-read alternative-walk matrix). Parse-time admission still runs before refusal. -/
def Expr.hasProjectedReferenceTo (expression : Expr) (model : FlatModel)
    (group : GroupPath) (target : FieldId) : Bool :=
  let namesTarget := fun reference : Reference =>
    reference.path.toFieldPath?.any fun path =>
      (model.resolveFieldDeclarationUnchecked group path).toOption.any (·.id == target)
  expression.anyReference fun reference =>
    ((reference.index.isSome || reference.category.isSome) && namesTarget reference) ||
      match reference.index with
      | some (.reference key) => key.anyReference namesTarget
      | _ => false

private def Expr.hasIndex : Expr → Bool := Expr.anyReference (·.index.isSome)

private def checkedHaving (result : Except CorrelationElabError α)
    (insideSemanticIndexKey : Bool := false) : Lowering α :=
  result.mapError fun error =>
    let capturedRead := match error with
      | .fieldOutsideEnvironment .outer .. | .repetitionOutsideEnvironment .outer ..
      | .outerLevelUnbound .. => true
      | _ => false
    { construct := "Having"
      detail := match error.diagnostic? with
        | some diagnostic =>
            if insideSemanticIndexKey && capturedRead && diagnostic == .noWildcard then
              KernelStaticDiagnostic.semanticIndexKeyInvalidIteration.kernelCode
            else diagnostic.kernelCode
        | none => oneLine ((repr error).pretty 100000) }



private structure RawAdmissionContext where
  compilePattern : StringPatternCompiler := locallyExecutableStringPatternMatcher?
  suppressExactScaleWarning : Bool := false
  inFilterSyntax : Bool := false

private abbrev RawAdmissionM := StateT FilterRuleFacts Lowering

mutual
/-- An entity key finishes its own read before its parent's semantic-index gates.
Inside an unmarked filter read, index and scope restrictions belong to the later body walk;
key applicability still precedes that walk. A reference's category follows its own index
cascade, so a nested index can refuse before that category (spec/07 §3, spec/08 §4). -/
private partial def admitEntityRead (model : FlatModel) (group bindingGroup : GroupPath)
    (reference : Reference) (inFilter insideSemanticIndexKey : Bool)
    (admission : RawAdmissionContext) : RawAdmissionM ((Sum FlatFieldDecl GroupPath) × Bool) := do
  let mut inFilter := inFilter
  let plain : Path := { reference.path with
    correlated := false
    segments := reference.path.segments.map fun segment => { segment with star := false } }
  let some field := plain.toFieldPath? | refuse "Having" "unsupported indexed entity path"
  let entity ← match model.groupNamedBy? group field with
    | some path => pure (.inr path)
    | none => do
        let source : SurfaceStarFieldPath := {
          base := reference.path.base, turningPoint := reference.path.turningPoint
          groups := reference.path.starGroups.dropLast, field := field.field }
        let declaration ← checkedHaving ((resolveStarFieldDeclaration model group source).mapError
          (CorrelationElabError.fieldFill ∘ FieldEntityShapeElabError.starPath))
        pure (.inl declaration)
  let targetPath := match entity with | .inl declaration => declaration.path | .inr path => path
  let basePath := targetPath.take (targetPath.length - reference.path.segments.length)
  if (firstStarOnNamedNonrepeatable? model basePath reference.path.starGroups).isSome then
    refuse "Having" KernelStaticDiagnostic.invalidWildcard.kernelCode
  let containingGroup := match entity with | .inl declaration => declaration.groupPath | .inr path => path
  let starredAt := fun position =>
    let offset := targetPath.length - reference.path.segments.length
    position >= offset && (reference.path.segments[position - offset]?).any (·.star)
  let mut indexedLevel : Option RepeatableLevel := none
  if let some key := reference.index then
    let checkedKey : Sum String ((Sum FlatFieldDecl GroupPath) × SemanticIndexAdmissionKeyRef) ← match key with
      | .literal spelling => pure (.inl spelling)
      | .reference keyReference => do
          let (keyEntity, keyInFilter) ← admitEntityRead model group bindingGroup keyReference inFilter true admission
          inFilter := keyInFilter
          pure (.inr (keyEntity, {
            resolvesToField := keyEntity.isLeft
            starred := keyReference.path.segments.any (·.star)
            expandsToNoValueValidation := match keyEntity with
              | .inl declaration => declaration.isRawString | .inr _ => false
            carriesCategory := keyReference.category.isSome }))
    let shapeKey : SemanticIndexAdmissionKey := match checkedKey with
      | .inl spelling => .constant spelling true
      | .inr (_, shape) => .reference shape
    if let some diagnostic := keyShapeRefusal shapeKey then
      refuse "Having" diagnostic.kernelCode
    if insideSemanticIndexKey then
      if let some diagnostic := semanticIndexAdmissionRefusal
          { valueSpecIsSemanticIndex := true } shapeKey then
        refuse "Having" diagnostic.kernelCode
    let groups := ((model.repeatableScopeForGroupPath containingGroup).filterMap
      model.repeatableGroupAtLevel?).reverse
    let indexPath := groups.map fun candidate => ({
      declaredNames := if candidate.indexField.isSome then 1 else 0
      nameResolvesToField := candidate.indexField.any fun id =>
        (model.lookupUniqueId id).toOption.any (·.groupPath == candidate.path) } : IndexDeclaringGroup)
    match indexResolution indexPath with
    | .error diagnostic => do refuse "Having" diagnostic.kernelCode
    | .ok none => do refuse "Having" KernelStaticDiagnostic.noIndexField.kernelCode
    | .ok (some _) => pure ()
    let some selected := groups.find? (·.indexField.isSome) | refuse "Having" "unresolved index group"
    let some id := selected.indexField | refuse "Having" "unresolved index field"
    let index ← checkedHaving ((model.lookupUniqueId id).mapError .resolve)
    let admissionKey ← match checkedKey with
      | .inl authored => do
          let matcher ← match index.stringPatternSource with
            | none => pure (fun (_ : String) => true)
            | some pattern => match admission.compilePattern pattern with
                | some matcher => pure matcher
                | none => do refuse "Having" "unsupported index pattern"
          let spelling := normalizeLinebreaks authored
          let some applicable := index.indexKeyFits? matcher authored | refuse "Having" "unsupported index kind"
          pure (SemanticIndexAdmissionKey.constant spelling applicable)
      | .inr (.inl keyDeclaration, shape) => pure (.reference { shape with
          baseTypeMatchesIndexField :=
            keyDeclaration.policy.kind.surfaceKind.sharesValueListBaseType index.policy.kind.surfaceKind
          containedInIndexGroup := selected.path.isPrefixOf keyDeclaration.groupPath })
      | .inr (.inr _, shape) => pure (.reference shape)
    let starredAtIndexLevel := starredAt (selected.path.length - 1)
    if let some diagnostic := semanticIndexAdmissionRefusal { indexPath, starredAtIndexLevel } admissionKey then
      refuse "Having" diagnostic.kernelCode
    indexedLevel := some selected.level
  let filteredBody ← reference.filter.mapM fun expression => do
    let .inl declaration := entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    let candidate := model.repeatableScopeForGroupPath declaration.groupPath
    let reopened := candidate.dropWhile fun level =>
      !(model.repeatableGroupAtLevel? level).any fun repeated => starredAt (repeated.path.length - 1)
    discard <| admitBody model group bindingGroup candidate reopened { admission with inFilterSyntax := true } insideSemanticIndexKey true expression
    pure (expression, candidate, reopened)
  -- Leaving a nested filter resets to ordinary rule reads, rather than restoring the enclosing
  -- filter mode (Lenient_ConditionParser.resetFilterCondition; spec/07 §3).
  let postReadInFilter := inFilter && filteredBody.isNone
  if reference.path.correlated && !postReadInFilter then
    refuse "Having" KernelStaticDiagnostic.invalidOuterIteration.kernelCode
  if reference.path.correlated || !postReadInFilter then
    let mut outerWildcard := false
    for level in model.repeatableScopeForGroupPath containingGroup do
      let some repeated := model.repeatableGroupAtLevel? level | refuse "Having" "unresolved captured repetition"
      if indexedLevel == some level then
        if outerWildcard then refuse "Having" IterationRefusal.semanticIndexBelowWildcard.catalogKey
      else if starredAt (repeated.path.length - 1) then
        outerWildcard := true
      else
        if !group.isPrefixOf bindingGroup then
          refuse "Having" KernelStaticDiagnostic.fieldNotInRuleGroup.kernelCode
        if let some refusal := levelIterationRefusal { marker := .iteration }
            outerWildcard insideSemanticIndexKey then
          refuse "Having" refusal.catalogKey
        let unbound := model.unboundOperandLevel group bindingGroup level
        if let some diagnostic := unbound.diagnostic? then
          refuse "Having" (if diagnostic == .noWildcard && insideSemanticIndexKey then
            KernelStaticDiagnostic.semanticIndexKeyInvalidIteration else diagnostic).kernelCode
        if unbound.parallelGate == .unmeasured then refuse "Having" "unsupported parallel reference"
        if unbound.parallelIterable then
          modify fun facts => { facts with
            parallelIteration := true
            parallelFilteredEntity := facts.parallelFilteredEntity || reference.filter.isSome
            parallelFilterBody := facts.parallelFilterBody || admission.inFilterSyntax }
  match entity with
  | .inl _ => pure ()
  | .inr path =>
      if !model.groupContributesField path then
        refuse "Having" path.emptyGroupDiagnostic.kernelCode
      if reference.category.isSome then refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
  if let some (expression, candidate, reopened) := filteredBody then
    if reopened.isEmpty then refuse "Having" KernelStaticDiagnostic.wildcardsRequired.kernelCode
    if reference.index.isSome then refuse "Having" KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
    let (references, forbidden) ← filterBodyInventoryAtLevels model group candidate reopened expression
    if let some diagnostic := filterBodyRefusal references forbidden then
      refuse "Having" diagnostic.kernelCode
  if let .inl declaration := entity then
    discard <| checkedHaving ((declaration.checkEntityCategoryRead (match reference.category with
      | none => .stored | some category => .projected category)).mapError .fieldFill)
  if admission.inFilterSyntax && reference.index.isSome then
    modify fun facts => { facts with filterUsesIndex := true }
  pure (entity, postReadInFilter)

/-- Lower and check each leaf in parse order before walking the complete body (spec/07 §3).
In particular, a later unsupported reader form cannot hide an earlier checked comparison error. -/
private partial def admitBody (model : FlatModel) (group bindingGroup : GroupPath)
    (candidateLevels reopenedLevels : List RepeatableLevel) (admission : RawAdmissionContext)
    (insideSemanticIndexKey inFilter : Bool) :
    Expr → RawAdmissionM (Option (SurfaceCorrelatedHaving × HavingBodyAdmission) × Bool)
  | .parens body => admitBody model group bindingGroup candidateLevels reopenedLevels admission insideSemanticIndexKey inFilter body
  | .custom name quoted => do
      let spelling := if quoted then CustomConditionNameSpelling.quoted name else .unquoted name
      let some _ := checkCustomConditionName (fun _ => false) spelling |
        refuse "CustomCondition" "invalid name"
      pure (none, inFilter)
  | .call "RepetitionNotUnique" arguments none scope => do
      modify fun facts => { facts with repetitionNotUniqueCount := facts.repetitionNotUniqueCount + 1 }
      let (keys, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission arguments
      let (scopeRead, state) ← match scope with
        | none => pure (none, state)
        | some reference => do
            let (reads, state) ← admitFieldList model group bindingGroup state insideSemanticIndexKey admission [.mk (.entity reference) none]
            let [read] := reads | refuse "Having" "repetition scope"
            pure (some read, state)
      checkRawRepetition model group keys scopeRead
      pure (none, state)
  | .logic operator (first :: rest) => do
      let join : CorrelatedHaving → CorrelatedHaving → CorrelatedHaving :=
        match operator with | .and => .and | .or => .or
      let (initial, initialState) ← admitBody model group bindingGroup candidateLevels reopenedLevels admission insideSemanticIndexKey inFilter first
      let mut body := initial
      let mut currentState := initialState
      for next in rest do
        let (following, nextState) ← admitBody model group bindingGroup candidateLevels reopenedLevels admission insideSemanticIndexKey currentState next
        currentState := nextState
        body := do
          let (leftAuthored, left) ← body
          let (rightAuthored, right) ← following
          let authored := match operator with
            | .and => SurfaceCorrelatedHaving.and leftAuthored rightAuthored
            | .or => SurfaceCorrelatedHaving.or leftAuthored rightAuthored
          pure (authored, HavingBodyAdmission.combine join left right)
      pure (body, currentState)
  | expression@(.call operator arguments (some members) none) => do
      if operator == "AtLeastOneDateRangeOverlaps" then
        let (subjects, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission arguments
        let (members, state) ← if members.all (fun | .mk (.string _) none => true | _ => false) then
            pure (none, state)
          else do
            let (reads, state) ← admitFieldList model group bindingGroup state insideSemanticIndexKey admission members
            pure (some reads, state)
        checkRawOverlapMembers model subjects members
        return (none, state)
      if (valueListQuantifier? operator).isSome then
        let (subjects, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission arguments
        let state ← match members.mapM (fun | .mk (.string value) none => some value | _ => none) with
          | some literals => do
              checkRawMembershipLiterals model false subjects literals false
              pure state
          | none => do
              let (members, state) ← admitFieldList model group bindingGroup state insideSemanticIndexKey admission members
              checkRawMembershipFields model false subjects members
              pure state
        return (none, state)
      if !inFilter then refuse "Having" "unsupported post-filter membership"
      let authored ← lowerHaving expression (some (model, group))
      let checked ← checkedHaving (elaborateHavingBodyAtLevels model group candidateLevels reopenedLevels authored bindingGroup admission.compilePattern) insideSemanticIndexKey
      pure (some (authored, checked), inFilter)
  | expression@(.call operator arguments none none) => do
      if operator == "FieldValuesNotUnique" || operator == "DateRangesOverlap" then
        let (reads, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission arguments
        checkRawListCondition model (operator == "DateRangesOverlap") reads
        return (none, state)
      if operator == "ValueNotConsistent" then
        return ← admitTableConsistency model group bindingGroup inFilter insideSemanticIndexKey admission arguments
      if operator == "Valid" || operator == "Invalid" then
        if let [.mk (.call "Date" components none none) none] := arguments then
          let (sources, state) ← admitConstructorComponents model group bindingGroup inFilter insideSemanticIndexKey admission components
          discard <| rawComponentConstructorType model .date sources
          if !sources.any (fun | .field .. => true | _ => false) then
            refuse "Having" KernelStaticDiagnostic.onlyConstantsUsed.kernelCode
          return (none, state)
        if let [.mk (.entity reference) none, .mk (.string name) none] := arguments then
          let (entity, state) ← admitEntityRead model group bindingGroup reference inFilter insideSemanticIndexKey admission
          let .inl declaration := entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
          if reference.path.segments.any (·.star) then refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
          if declaration.isRawString then refuse "Having" KernelStaticDiagnostic.rawTypeOperandInvalid.kernelCode
          discard <| checkedHaving ((elaborateCustomFieldValidityOperand model declaration.id).mapError .typeValidityOperand)
          if name.isEmpty then refuse "Having" KernelStaticDiagnostic.noEmpty.kernelCode
          return (none, state)
      if operator == "FieldValueIncludedInValueList" || operator == "FieldValueNotIncludedInValueList" then
        if let subject :: members := arguments then
          if members.all (fun | .mk (.value _) none => true | _ => false) then
            let (subjects, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission [subject]
            let (members, state) ← admitFieldValues model group bindingGroup state insideSemanticIndexKey admission members
            checkRawMembershipFields model true subjects members
            return (none, state)
          else
            let (subjects, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission [subject]
            if let some literals := members.mapM (fun | .mk (.string value) none => some value | _ => none) then
              checkRawMembershipLiterals model true subjects literals false
            else if members.all (fun | .mk (.number _) none => true | _ => false) then
              for member in members do
                let .mk (.number text) none := member | refuse "Having" "integer member"
                let some literal := decodeNumber? text | refuse "Having" "integer member"
                if literal.authoredScale != 0 then refuse "Having" "integer member"
              checkRawMembershipLiterals model true subjects [] true
            else refuse "Having" "membership literal form"
            return (none, state)
      if let [.mk (.entity reference) none] := arguments then
        if operator == "FieldFilled" || operator == "FieldNotFilled" then
          let (entity, currentState) ← admitEntityRead model group bindingGroup reference inFilter insideSemanticIndexKey admission
          if let .inr path := entity then
            if path.length == 1 then
              discard <| checkedHaving (Except.error (.fieldFill (.rootGroupOperand path)) : Except CorrelationElabError Unit)
          if reference.category.isSome then
            refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
          if entity.isRight then refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
          if reference.path.segments.any (·.star) then
            refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
          -- Executable environment binding follows the whole-rule gates; a captured parallel
          -- read must reach those gates first (ParserService.checkNormalRule; spec/07 §3).
          return (none, currentState)
      let groupOperator := if operator == "GroupFilled" || operator == "GroupNotFilled" then
        some RawGroupOperator.presence else RawGroupOperator.quantifier <$> groupQuantifier? operator
      if let some groupOperator := groupOperator then
        let (reads, currentState) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission arguments
        checkRawGroupBody groupOperator reads
        return (none, currentState)
      if let some quantifier := fieldFillOp? operator then
        let (reads, currentState) ← admitFieldList model group bindingGroup inFilter
          insideSemanticIndexKey admission arguments
        checkRawListDuplicates reads
        checkRawListRoots reads
        if reads.any (·.reference.category.isSome) then
          refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
        let manyRequired := match quantifier with
          | .noFieldFilled | .atLeastOneFieldFilled => false
          | _ => true
        if manyRequired && reads.length < 2 && !reads.any (·.isMany) then
          refuse "Having" KernelStaticDiagnostic.paramSizeInvalidN.kernelCode
        return (none, currentState)
      if !inFilter then refuse "Having" "unsupported post-filter operator"
      let authored ← lowerHaving expression (some (model, group))
      let checked ← checkedHaving (elaborateHavingBodyAtLevels model group candidateLevels reopenedLevels authored bindingGroup admission.compilePattern) insideSemanticIndexKey
      pure (some (authored, checked), inFilter)
  | expression@(.compare op left right) => do
      if op == .patternMatched || op == .patternViolated then
        let (leftKind, state) ← admitPatternOperand model group bindingGroup inFilter insideSemanticIndexKey admission left
        let (rightKind, state) ← admitPatternOperand model group bindingGroup state insideSemanticIndexKey admission right
        discard <| checkedHaving ((checkComparisonEntry .pattern
          (rawComparisonEntry leftKind left) (rawComparisonEntry rightKind right)).mapError .comparisonEntry)
        let some source := right.patternConstant? | refuse "Having" "pattern constant"
        discard <| checkedHaving ((admitStringPattern admission.compilePattern source).mapError
          (CorrelationElabError.stringPattern ∘ StringPatternConditionElabError.pattern))
        return (none, state)
      let scalarTrees := rawScalarTreeAvailable left && rawScalarTreeAvailable right
      if expression.needsOrderedAdmission || expression.hasIndex || !inFilter || scalarTrees then
        let leftSource := left
        let rightSource := right
        let (left, nextState) ← admitNumericExpression model group bindingGroup inFilter insideSemanticIndexKey admission left
        let (right, finalState) ← admitNumericExpression model group bindingGroup nextState insideSemanticIndexKey admission right
        checkRawComparisonOperands model op leftSource rightSource left right admission.suppressExactScaleWarning
        return (none, finalState)
      let authored ← lowerHaving expression (some (model, group))
      let checked ← checkedHaving (elaborateHavingBodyAtLevels model group candidateLevels reopenedLevels authored bindingGroup admission.compilePattern) insideSemanticIndexKey
      pure (some (authored, checked), inFilter)
  | expression => do
      if !inFilter then refuse "Having" "unsupported post-filter expression"
      let authored ← lowerHaving expression (some (model, group))
      let checked ← checkedHaving (elaborateHavingBodyAtLevels model group candidateLevels reopenedLevels authored bindingGroup admission.compilePattern) insideSemanticIndexKey
      pure (some (authored, checked), inFilter)

/-- All entity parameters finish their own reads before the table gate. The existing A12 table
view settles the refusal independently of declared field kind (spec/06; CheckFieldAndValueListConditionImpl). -/
private partial def admitTableConsistency (model : FlatModel) (group bindingGroup : GroupPath)
    (inFilter insideSemanticIndexKey : Bool) (admission : RawAdmissionContext)
    (arguments : List Argument) : RawAdmissionM (Option (SurfaceCorrelatedHaving × HavingBodyAdmission) × Bool) := do
  let .mk (.entity reference) (some firstParameter) :: rest := arguments |
    refuse "Having" "table-consistency operands"
  let (entity, initialState) ← admitEntityRead model group bindingGroup reference inFilter insideSemanticIndexKey admission
  let mut state := initialState
  let mut parameters := []
  for parameter in Argument.mk firstParameter none :: rest do
    let value ← match parameter with
      | .mk (.string value) none => pure (.stringLiteral value)
      | .mk (.entity parameter) none => do
          let (entity, nextState) ← admitEntityRead model group bindingGroup parameter state insideSemanticIndexKey admission
          state := nextState
          match entity with
          | .inl declaration => match declaration.enumeration with
              | some enumeration => pure (.enumerationField enumeration.storedTokens)
              | none => pure .otherKind
          | .inr _ => pure .otherKind
      | _ => do refuse "Having" "table-consistency parameter"
    parameters := parameters ++ [value]
  let values := match entity with
    | .inl declaration => declaration.enumeration.map (·.storedTokens) |>.getD []
    | .inr _ => []
  let operand : TableConsistencyOperand := {
    isField := entity.isLeft
    hasWildcard := reference.path.segments.any (·.star)
    declaration := a12TableView values }
  match valueNotConsistentRefusal operand parameters with
  | some refusal => do refuse "Having" refusal.catalogKey
  | none => do refuse "Having" "unsupported table enumeration"

/-- Pattern comparison retains declared result kinds, rather than numeric string-like coercions.
Both sides finish their own reads before comparison entry (CheckVergleichsBedingungImpl; spec/06 Part A). -/
private partial def admitPatternOperand (model : FlatModel) (group bindingGroup : GroupPath)
    (inFilter insideSemanticIndexKey : Bool) (admission : RawAdmissionContext) :
    Expr → RawAdmissionM (SurfaceScalarKind × Bool)
  | .value reference => do
      let (reads, state) ← admitFieldValues model group bindingGroup inFilter insideSemanticIndexKey admission [.mk (.value reference) none]
      let [{ entity := .inl declaration, .. }] := reads | refuse "Having" "pattern field"
      pure (declaration.policy.kind.surfaceKind, state)
  | .braces body | .parens body => admitPatternOperand model group bindingGroup inFilter insideSemanticIndexKey admission body
  | .string text => pure (
      if (civilDateConstant? text).isSome || (yearlessDateConstant? text).isSome then .temporal .date
      else if (timeConstant? text).isSome then .temporal .time
      else if (dateTimeConstant? text).isSome then .temporal .dateTime else .string, inFilter)
  | .entity _ => do refuse "Having" "bare pattern operand"
  | .constant "Today" => pure (.temporal .date, inFilter)
  | .constant "Now" => pure (.temporal .dateTime, inFilter)
  | expression => do
      let (tree, state) ← admitNumericExpression model group bindingGroup inFilter insideSemanticIndexKey admission expression
      let type ← rawNumericType model.hasBaseYear tree
      pure (type.surfaceKind, state)

private partial def admitFieldValues (model : FlatModel) (group bindingGroup : GroupPath)
    (inFilter insideSemanticIndexKey : Bool) (admission : RawAdmissionContext)
    (arguments : List Argument) : RawAdmissionM (List RawListRead × Bool) := do
  let mut state := inFilter
  let mut values := []
  for argument in arguments do
    let .mk (.value reference) none := argument | refuse "Having" "field value read"
    let (reads, nextState) ← admitFieldList model group bindingGroup state insideSemanticIndexKey admission [.mk (.entity reference) none]
    state := nextState
    let [read] := reads | refuse "Having" "field value read"
    let .inl declaration := read.entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    if reference.path.segments.any (·.star) then refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
    if let some error := declaration.projectedReadRefusal? (reference.category.map EnumerationProjectionRef.category |>.getD .stored) then
      discard <| checkedHaving (Except.error (.resolve error) : Except CorrelationElabError Unit)
    values := values ++ [read]
  pure (values, state)

/-- Finish every own read before list-level shape/type gates. Keep static key identity even when
an enclosing filter will reject the indexed reference; no runtime indexed certificate is needed
(CheckEntityListenUtils.getRefList; spec/07 §3, spec/08 §4). -/
private partial def admitFieldList (model : FlatModel) (group bindingGroup : GroupPath)
    (inFilter insideSemanticIndexKey : Bool) (admission : RawAdmissionContext)
    (arguments : List Argument) : RawAdmissionM (List RawListRead × Bool) := do
  let mut currentState := inFilter
  let mut operands := []
  for argument in arguments do
    let reference ← match argument with
      | .mk (.entity reference) none => pure reference
      | .mk (.constant "RuleGroup") none =>
          pure ({ path := { absolute := true, segments := group.map fun name => { name, star := false } } } : Reference)
      | _ => do refuse "Having" "raw field-list operand"
    let (entity, nextState) ← admitEntityRead model group bindingGroup reference currentState insideSemanticIndexKey admission
    currentState := nextState
    let key ← reference.index.mapM fun key => match key with
      | .literal spelling => pure (.literal spelling)
      | .reference keyReference => do
          -- Own-read admission already settled the key's legality. Canonicalize only its field
          -- identity here, so relative/absolute aliases compare alike without replaying reads.
          let some source := { keyReference.path with correlated := false }.toStarFieldPath? |
            refuse "Having" "unresolved admitted list key"
          let declaration ← checkedHaving ((resolveStarFieldDeclaration model group source).mapError
            (CorrelationElabError.fieldFill ∘ FieldEntityShapeElabError.starPath))
          pure (.field declaration.id keyReference.path.correlated)
    operands := operands ++ [{ reference, entity, key }]
  pure (operands, currentState)

/-- The shared syntax reader discharges each operation before its next sibling, while the
atom callbacks preserve parser read state (CheckRundenOpImpl; CheckOperationImpl). -/
private partial def admitNumericExpression (model : FlatModel) (group bindingGroup : GroupPath)
    (inFilter insideSemanticIndexKey : Bool) (admission : RawAdmissionContext)
    (expression : Expr) : RawAdmissionM (AuthoredNumericExpr NumericOperandType × Bool) := do
  letI : Nonempty (StateT Bool RawAdmissionM (AuthoredNumericExpr NumericOperandType)) :=
    ⟨throw { construct := "Having" }⟩
  let atom (source : Expr) : StateT Bool RawAdmissionM NumericOperandType := do
    let (type, state) ← liftM <| admitNumericAtom model group bindingGroup (← get) insideSemanticIndexKey admission source
    set state
    pure type
  let fieldAtom (source : Expr) : StateT Bool RawAdmissionM NumericOperandType := do
    let reference ← liftM <| numericFieldFormReference source
    let (reads, state) ← liftM <| admitFieldList model group bindingGroup (← get) insideSemanticIndexKey admission [.mk (.entity reference) none]
    set state
    let [{ reference, entity := .inl declaration, .. }] := reads |
      liftM <| refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
    if reference.path.segments.any (·.star) then
      liftM <| refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
    if reference.category.isSome then
      liftM <| refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
    let .number info := declaration.policy.kind |
      liftM <| refuse "Having" KernelStaticDiagnostic.noNumber.kernelCode
    pure (.number (.field info.scale))
  let beforeRounding (source : Expr) (tree : AuthoredNumericExpr NumericOperandType) : StateT Bool RawAdmissionM Unit :=
    liftM <| checkRawNumericWrapper model.hasBaseYear source tree
  let complete (source : Expr) (tree : AuthoredNumericExpr NumericOperandType) : StateT Bool RawAdmissionM Unit :=
    liftM <| checkRawNumericOperation model.hasBaseYear source tree
  (lowerNumericExprWith atom fieldAtom beforeRounding complete expression).run inFilter

private partial def admitTemporalOperand (model : FlatModel) (group bindingGroup : GroupPath)
    (inFilter insideSemanticIndexKey : Bool) (admission : RawAdmissionContext) (allowCompletion : Bool := false) :
    Expr → RawAdmissionM (NumericOperandType × Option FlatFieldDecl × Bool)
  | source@(.entity _) | source@(.constant "RuleGroup") => do
      let (reads, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission [.mk source none]
      let [read] := reads | refuse "Having" "temporal source field"
      let (type, declaration) ← rawTemporalField read.reference read.entity
      pure (type, some declaration, state)
  | .string text => return (← rawTemporalLiteral text, none, inFilter)
  | .constant "Today" => pure (.temporal .date .today, none, inFilter)
  | .constant "Now" => pure (.temporal .dateTime .now, none, inFilter)
  | .constant "BaseYear" =>
      if model.baseYear.isSome then pure (.temporal .date .baseYear, none, inFilter)
      else refuse "Having" KernelStaticDiagnostic.conditionNoBaseYear.kernelCode
  | .call "ValueAsDate" [.mk source none, .mk (.constant endpoint) none] none none => do
      if !allowCompletion || !["FirstDay", "LastDay"].contains endpoint then refuse "Having" "partial temporal source"
      let (reads, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission [.mk source none]
      let [read] := reads | refuse "Having" "partial temporal field"
      return (← rawValueAsDateType read.reference read.entity, none, state)
  | source@(.call id _ none none) => do
      let allowed := (rawTemporalExtractor? id).isSome || (rawTemporalConstructor? id).isSome || isRawRangeBound id ||
        (match rawTemporalArithmetic? id with | some (.shift _) => true | _ => false)
      if !allowed then refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
      let (type, state) ← admitNumericAtom model group bindingGroup inFilter insideSemanticIndexKey admission source
      let .temporal .. := type | refuse "Having" KernelStaticDiagnostic.invalidDateForOp.kernelCode
      pure (type, none, state)
  | _ => do refuse "Having" "temporal source"

/-- Constructor field policies wait until all component children have completed; extractor
children still discharge their own gates immediately (CheckBaseDateConstructionImpl). -/
private partial def admitConstructorComponents (model : FlatModel) (group bindingGroup : GroupPath)
    (inFilter insideSemanticIndexKey : Bool) (admission : RawAdmissionContext)
    (arguments : List Argument) : RawAdmissionM (List RawConstructorComponent × Bool) := do
  let mut state := inFilter
  let mut components := []
  for argument in arguments do
    let (component, nextState) : RawConstructorComponent × Bool ← match argument with
      | .mk (.string text) none => pure (.literal text, state)
      | .mk (.entity _) none | .mk (.constant "RuleGroup") none => do
          let (reads, afterRead) ← admitFieldList model group bindingGroup state insideSemanticIndexKey admission [argument]
          let [read] := reads | refuse "Having" "constructor field"
          pure (.field read.reference read.entity, afterRead)
      | .mk source@(.call name _ none none) none => do
          let some operator := rawTemporalExtractor? name | refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
          let (_, afterRead) ← admitNumericAtom model group bindingGroup state insideSemanticIndexKey admission source
          pure (.extractor operator, afterRead)
      | _ => do refuse "Syntax" SyntaxErrorClass.unexpectedToken.code
    components := components ++ [component]
    state := nextState
  pure (components, state)

private partial def admitNumericAtom (model : FlatModel) (group bindingGroup : GroupPath)
    (inFilter insideSemanticIndexKey : Bool) (admission : RawAdmissionContext) :
    Expr → RawAdmissionM (NumericOperandType × Bool)
  | .entity reference | .value reference => do
      let (entity, state) ← admitEntityRead model group bindingGroup reference inFilter insideSemanticIndexKey admission
      let .inl declaration := entity | refuse "Having" KernelStaticDiagnostic.noGroupsAllowed.kernelCode
      if reference.path.segments.any (·.star) then
        refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
      if reference.category.isNone then
        if let some error := declaration.fieldValueReadRefusal? then
          discard <| checkedHaving (Except.error (.resolve error) : Except CorrelationElabError Unit)
      let type := NumericOperandType.ofDeclaration declaration
      if let some category := reference.category then
        let some source := declaration.enumeration.bind (fun source => source.categories.find? (·.name == category)) |
          refuse "Having" "unresolved category result"
        return (.enumeration .category source.tokens, state)
      pure (type, state)
  | .call "CurrentRepetition" [argument] none none => do
      let (reads, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission [argument]
      let [{ reference, entity := .inr _, .. }] := reads |
        refuse "Having" KernelStaticDiagnostic.noFieldsAllowed.kernelCode
      if reference.path.segments.any (·.star) then
        refuse "Having" KernelStaticDiagnostic.noWildcardsAllowed.kernelCode
      pure (.number (.field 0), state)
  | .call "NumberOfValueInFields" [.mk expected none] (some arguments) none => do
      let (reads, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission arguments
      checkRawValueCount model reads expected
      pure (.number (.field 0), state)
  | .call id arguments none none => do
      if id == "DateRange" then
        let (reads, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission arguments
        return (← rawDateRangeConstructorType (reads.map fun read => (read.reference, read.entity)), state)
      if let some constructor := rawTemporalConstructor? id then
        if constructor == .dateTime then
          let [.mk date none, .mk time none] := arguments | refuse "Having" "DateTime arguments"
          let (dateType, direct, state) ← admitTemporalOperand model group bindingGroup inFilter insideSemanticIndexKey admission true date
          let (timeType, _, state) ← admitTemporalOperand model group bindingGroup state insideSemanticIndexKey admission false time
          return (← rawDateTimeConstructorType model dateType direct timeType, state)
        let (components, state) ← admitConstructorComponents model group bindingGroup inFilter insideSemanticIndexKey admission arguments
        return (← rawComponentConstructorType model constructor components, state)
      if let some operator := rawTemporalExtractor? id then
        let [.mk source none] := arguments | refuse "Having" "temporal extractor argument"
        let (type, declaration, state) ← admitTemporalOperand model group bindingGroup inFilter insideSemanticIndexKey admission false source
        let literal := match source with | .string _ => true | _ => false
        return (← rawTemporalExtractorType model operator type literal declaration, state)
      if let some operator := rawTemporalArithmetic? id then
        let [.mk first none, .mk second none] := arguments | refuse "Having" "temporal arithmetic arguments"
        let (firstType, firstDeclaration, state) ← admitTemporalOperand model group bindingGroup inFilter insideSemanticIndexKey admission true first
        match operator with
        | .shift unit =>
            let (tree, state) ← admitNumericExpression model group bindingGroup state insideSemanticIndexKey admission second
            return (← rawTemporalShiftType model unit firstType firstDeclaration (← rawNumericType model.hasBaseYear tree), state)
        | .difference unit =>
            let (secondType, secondDeclaration, state) ← admitTemporalOperand model group bindingGroup state insideSemanticIndexKey admission true second
            return (← rawTemporalDifferenceType model unit (firstType, firstDeclaration) (secondType, secondDeclaration), state)
      if isRawRangeBound id then
        let [.mk source none] := arguments | refuse "Having" "range endpoint argument"
        if let .constant "BaseYear" := source then
          let (type, _, state) ← admitTemporalOperand model group bindingGroup inFilter insideSemanticIndexKey admission false source
          return (type, state)
        let (reads, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission [.mk source none]
        let [read] := reads | refuse "Having" "range endpoint field"
        return (← rawRangeBoundType read.reference read.entity, state)
      if let some operator := rawScalarOperator? id then
        let first :: rest := arguments | refuse "Having" "scalar operation field"
        let (reads, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission [first]
        let [read] := reads | refuse "Having" "scalar operation field"
        let bounds ← match operator, rest with
          | .rangeNumber, [.mk (.number start) none, .mk (.number finish) none]
          | .rangeString, [.mk (.number start) none, .mk (.number finish) none] => do
              let some start := start.toNat? | refuse "Having" "range start"
              let some finish := finish.toNat? | refuse "Having" "range finish"
              pure (some (start, finish))
          | .length, [] | .asNumber, [] | .asString, [] => pure none
          | _, _ => do refuse "Having" "scalar operation arguments"
        let type ← rawScalarType operator read.reference read.entity bounds
        if operator == .length then
          if let .inl declaration := read.entity then
            if declaration.isRawString then modify fun facts => { facts with rawLength := true }
        return (type, state)
      let some operator := rawListOperator? id | refuse "Having" "raw numeric atom"
      let (reads, state) ← admitFieldList model group bindingGroup inFilter insideSemanticIndexKey admission arguments
      if (operator == .filledCount || operator == .groupCount || operator == .aggregate .distinctCount) &&
          reads.any (·.reference.category.isSome) then
        refuse "Having" KernelStaticDiagnostic.categoryNotAllowed.kernelCode
      checkRawListDuplicates reads
      checkRawListRoots reads (operator == .groupCount)
      if operator == .groupCount then
        if reads.any (·.key.isSome) then refuse "Having" KernelStaticDiagnostic.semanticIndexNotAllowed.kernelCode
        if reads.any (·.entity.isLeft) then refuse "Having" KernelStaticDiagnostic.noFieldsAllowed.kernelCode
        if reads.length < 2 && !reads.any (fun read => read.reference.path.segments.any (·.star)) then
          refuse "Having" KernelStaticDiagnostic.paramSizeInvalidGN.kernelCode
        return (.number (.field 0), state)
      if operator == .product then return (← rawProductType model reads, state)
      if reads.length < 2 && !reads.any (·.isMany) then
        refuse "Having" KernelStaticDiagnostic.paramSizeInvalidN.kernelCode
      let declarations := reads.flatMap (·.declarations model)
      match operator with
      | .filledCount => return (.number (.field 0), state)
      | .firstFilled => return (← rawFirstFilledType declarations, state)
      | _ => pure ()
      let .aggregate op := operator | refuse "Having" "raw numeric atom"
      let types := reads.flatMap fun read => (read.declarations model).map fun declaration =>
        if read.reference.category.isNone then NumericOperandType.ofDeclaration declaration else .stringLike
      let first :: rest := types | refuse "Having" "empty numeric expansion"
      match op with
      | .sum =>
          let .number initial := first | refuse "Having" KernelStaticDiagnostic.noNumber.kernelCode
          let mut scale := initial
          for type in rest do
            let .number next := type | refuse "Having" KernelStaticDiagnostic.noNumber.kernelCode
            scale := scale.union next
          pure (.number scale, state)
      | .minimum | .maximum => do
          if let .temporal _ components := first then
            checkRawTemporalList model components (reads.flatMap (·.declarations model))
            return (first, state)
          let operator := if op == .minimum then NumericExtremumOp.minimum else .maximum
          let tree := AuthoredNumericExpr.extremumCall operator
            (rest.foldl (fun tree type => .extremum operator tree (.atom type)) (.atom first))
          pure (← rawNumericType model.hasBaseYear tree, state)
      | .distinctCount => do
          checkRawDistinctTypes model (reads.flatMap (·.declarations model))
          pure (.number (.field 0), state)
  | .string value =>
      if isTemporalConstant value then return (← rawTemporalLiteral value, inFilter)
      else pure (.stringLike, inFilter)
  | .constant "True" | .constant "False" => pure (.other .boolean, inFilter)
  | .constant "Today" => pure (.temporal .date .today, inFilter)
  | .constant "Now" => pure (.temporal .dateTime .now, inFilter)
  | .constant "BaseYear" =>
      if model.hasBaseYear then pure (.number (.field 0), inFilter)
      else refuse "Having" KernelStaticDiagnostic.conditionNoBaseYear.kernelCode
  -- An operation's operand is arithmetic, so a comparison or connective there is a token defect at
  -- its operator; the operand read before it completed its own production and keeps that check
  -- (`Abs(RoundUpValue(Reference, 2) > 1) > 0` draws `MVK_NO_NUMBER`, `Max([Score] > 1, 2)` the
  -- token class; spec/12 §12.3).
  | .compare _ left _ => do
      discard <| admitNumericExpression model group bindingGroup inFilter insideSemanticIndexKey admission left
      refuse "Having" KernelStaticDiagnostic.unexpectedToken.kernelCode
  | .logic _ (first :: _) => do
      discard <| admitBody model group bindingGroup [] [] admission insideSemanticIndexKey inFilter first
      refuse "Having" KernelStaticDiagnostic.unexpectedToken.kernelCode
  | _ => do refuse "Having" "raw numeric atom"

end

/-- Admit constructor/filter children before lowering and whole-rule gates. Their authored
read order precedes enclosing checks (KF532; ParserService.checkNormalRule; spec/07 §3). -/
def checkOrderedAdmission (model : FlatModel) (group bindingGroup : GroupPath)
    (expression : Expr) (suppressExactScaleWarning : Bool := false) : Lowering Unit := do
  if !expression.needsOrderedAdmission then return
  let (_, facts) ← (admitBody model group bindingGroup [] [] { suppressExactScaleWarning } false false expression).run {}
  -- Having requires a star while Length forbids stars, so this is not the standalone limiter exception (CheckFeldOpImpl; AnalyseService).
  if expression.hasHaving then
    if let some diagnostic := facts.beforeIterationRefusal? then refuse "Having" diagnostic.kernelCode

/-- Admit one fragment and retain its contribution to the generated rule's global checks. -/
def checkRawConditionBeforeGlobals (model : FlatModel) (group bindingGroup : GroupPath)
    (expression : Expr) (suppressExactScaleWarning : Bool) : Lowering FilterRuleFacts := do
  let (_, facts) ← (admitBody model group bindingGroup [] [] { suppressExactScaleWarning } false false expression).run {}
  pure facts

/-- The generated target bracket is read before the authored operation (spec/09 §6). -/
def rawComputationTarget (target : FlatFieldDecl) : Expr :=
  .value { path := { absolute := true, segments := target.path.map fun name => { name, star := false } } }

/-- Check only the generated bracket before parsing the operation it will compare. -/
def checkRawComputationTargetRead (model : FlatModel) (group : GroupPath) (target : FlatFieldDecl) : Lowering Unit := do
  discard <| (admitNumericAtom model group target.groupPath false false {} (rawComputationTarget target)).run' {}

/-- Finish one ordinary authored reference read before advancing to another operand. The original
reference remains available to the caller's kind/shape and executable lowering stages (spec/07 §3). -/
def checkReferenceRead (model : FlatModel) (group bindingGroup : GroupPath) (reference : Reference) :
    Lowering Unit := do
  discard <| checkedHaving (model.validate.mapError .resolve)
  discard <| (admitEntityRead model group bindingGroup reference false false {}).run' {}

/-- Admit a parsed body at an already checked filtered field. This entry preserves the raw
reference walk after ordered own-leaf checks, then certifies the executable body. Parser exit
state is carried independently of executable-body availability (spec/07 §3). -/
private def admitRawStarHaving (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (expression : Expr)
    (bindingGroup : GroupPath := declaringGroup)
    (compilePattern : StringPatternCompiler := locallyExecutableStringPatternMatcher?) :
    Lowering (SurfaceCorrelatedHaving × CheckedStarHaving model source bindingGroup) := do
  let candidate := source.path.axes.map (·.level)
  let (body, _) ← (admitBody model declaringGroup bindingGroup candidate (candidate.drop source.path.firstStar)
    { compilePattern, inFilterSyntax := true } false true expression).run' {}
  let (references, forbidden) ← filterBodyInventory model declaringGroup source expression
  if let some diagnostic := filterBodyRefusal references forbidden then
    refuse "Having" diagnostic.kernelCode
  let (authored, body) ← match body with
    | some checked => pure checked
    | none => do
        if expression.hasIndex || expression.hasHaving then refuse "Having" "indexed body escaped its filter walk"
        -- Certify the unchanged ordinary tree only after its complete own-read pass and filter walk.
        -- This keeps late typed restrictions behind later parse-time failures (spec/07 §3).
        let authored ← lowerHaving expression (some (model, declaringGroup))
        let checked ← checkedHaving (elaborateHavingBodyAtLevels model declaringGroup candidate
          (candidate.drop source.path.firstStar) authored bindingGroup compilePattern)
        pure (authored, checked)
  let checked ← checkedHaving (finishStarHavingBody model declaringGroup source body bindingGroup)
  pure (authored, checked)

def elaborateRawStarHaving (model : FlatModel) (declaringGroup : GroupPath)
    (source : CheckedStarFieldPath model) (expression : Expr)
    (bindingGroup : GroupPath := declaringGroup)
    (compilePattern : StringPatternCompiler := locallyExecutableStringPatternMatcher?) :
    Lowering (CheckedStarHaving model source bindingGroup) :=
  Prod.snd <$> admitRawStarHaving model declaringGroup source expression bindingGroup compilePattern

/-- A reader with a known caller binding checks the raw body before returning the existing
surface tree. Callers without that context retain their deferred typed admission. -/
def lowerAdmittedHaving (model : FlatModel) (group : GroupPath) (path : SurfaceStarFieldPath)
    (expression : Expr) (bindingGroup? : Option GroupPath) : Lowering SurfaceCorrelatedHaving := do
  match bindingGroup? with
  | none => lowerHaving expression (some (model, group))
  | some bindingGroup =>
      let source ← checkedHaving ((elaborateStarFieldPath model group path).mapError (CorrelationElabError.fieldFill ∘ FieldEntityShapeElabError.starPath))
      Prod.fst <$> admitRawStarHaving model group source expression bindingGroup

end A12Kernel.Dm
