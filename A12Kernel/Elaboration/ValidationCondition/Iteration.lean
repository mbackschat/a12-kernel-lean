import A12Kernel.Elaboration.ValidationCondition.StaticIteration

/-! # Validation-condition iteration legality and addressed execution -/

namespace A12Kernel

namespace DecodedNumericLiteral

/-- Compatibility specialization for the established iteration-legality consumer. -/
def iterationHostInt32? := javaRoundedInt32?

end DecodedNumericLiteral

namespace ValidationCondition

private def hostConvertedLiteralValue? :
    AuthoredNumericExpr Atom → Option Int
  | .literal literal => literal.iterationHostInt32?
  | _ => none

/-- Apply the source-closed host-converted literal partition after an exact operand-shape recognizer supplies its model-owned scope. -/
private def orderedNumericScopedLiteralGuardAt
    (scopeOf :
      AuthoredNumericExpr (OrderedNumericValidationAtom model) →
        Option (List RepeatableLevel))
    (level : RepeatableLevel)
    (comparison : OrderedNumericComparison model) :
    Option IterationGuardStatus :=
  let classify scopedExpr literalExpr := do
    let scope ← scopeOf scopedExpr
    let literal ← hostConvertedLiteralValue? literalExpr
    if scope.contains level then
      if literal == 0 && directEmptyZeroIsUnguarded comparison.op then
        some .unguarded
      else
        some .guarded
    else
      some .noReference
  match classify comparison.left comparison.right with
  | some status => some status
  | none => classify comparison.right comparison.left

private def orderedNumericDirectFieldLiteralGuardAt
    (level : RepeatableLevel)
    (comparison : OrderedNumericComparison model) :
    Option IterationGuardStatus :=
  orderedNumericScopedLiteralGuardAt
    (directOrdinaryZeroSensitiveScope? model) level comparison

/-- Collect only direct Number references from one operation-list body without flattening away their model-owned scopes. Specialized entity-list atoms retain their separate packet. -/
private def directOrdinaryNumberReferenceScopes?
    (model : FlatModel) :
    AuthoredNumericExpr (OrderedNumericValidationAtom model) →
      Option (List (List RepeatableLevel))
  | expression@(.atom (.ordinary (.field _))) => do
      let scope ← directOrdinaryZeroSensitiveScope? model expression
      pure [scope]
  | .literal _ => some []
  | .group body | .abs body | .extremumCall _ body
  | .round _ _ body =>
      directOrdinaryNumberReferenceScopes? model body
  | .binary _ left right | .power left right | .extremum _ left right => do
      let leftScopes ← directOrdinaryNumberReferenceScopes? model left
      let rightScopes ← directOrdinaryNumberReferenceScopes? model right
      pure (leftScopes ++ rightScopes)
  | .atom _ => none

private inductive LevelReferenceShape where
  | none
  | allIterating
  | mixed

private def levelReferenceShapeAt (level : RepeatableLevel)
    (scopes : List (List RepeatableLevel)) : LevelReferenceShape :=
  let iterating := scopes.map (·.contains level)
  if iterating.any id then
    if iterating.all id then .allIterating else .mixed
  else
    .none

/-- Direct-field `Abs`, rounding, and Min/Max are operation-list consumers of the same per-level reference classifier. -/
private def directNumberWrapperReferenceScopes?
    (model : FlatModel) :
    AuthoredNumericExpr (OrderedNumericValidationAtom model) →
      Option (List (List RepeatableLevel))
  | .group body => directNumberWrapperReferenceScopes? model body
  | .abs body | .round _ _ body | .extremumCall _ body =>
      directOrdinaryNumberReferenceScopes? model body
  | _ => none

private def orderedNumericDirectWrapperLiteralGuardAt
    (level : RepeatableLevel)
    (comparison : OrderedNumericComparison model) :
    Option IterationGuardStatus :=
  let classify wrapperExpr literalExpr := do
    let scopes ← directNumberWrapperReferenceScopes? model wrapperExpr
    match literalExpr with
    | .literal _ =>
        match levelReferenceShapeAt level scopes with
        | .none => some .noReference
        | .mixed => some .unguarded
        | .allIterating =>
            let literal ← hostConvertedLiteralValue? literalExpr
            if literal == 0 &&
                directEmptyZeroIsUnguarded comparison.op then
              some .unguarded
            else
              some .guarded
    | _ => none
  match classify comparison.left comparison.right with
  | some status => some status
  | none => classify comparison.right comparison.left

/-- A selected entity still references its enclosing parent and dynamic key scopes. The selected level itself is supplied by lookup (`SemanticIndex.bindingScopes`); the Kernel's `IterationNotValidVisitor.isIteration(IEntityId)` also follows the key's iteration. -/
private def selectedEntityGuardScope
    (source : Sum (CheckedSemanticIndexSource model) (CheckedKeyedEntityExtent model)) :
    List RepeatableLevel :=
  (match source with | .inl source => source.bindingScopes | .inr source => source.bindingScopes).flatten

private def numberEntityOperandReferenceScope? :
    CheckedNumberEntityOperand model →
      Option (List RepeatableLevel)
  | .field source => some source.declaration.repeatableScope
  | .selected source => some (selectedEntityGuardScope source.source)
  | .star checked => checkedStarBindingScope checked.source
  | .starHaving checked => checkedStarBindingScope checked.source.source
  | .group slot =>
      let scope := slot.source.bindingScope
      if scope.isEmpty then some [] else some scope

private def numberEntityReferenceScopes?
    (source : CheckedNumberEntitySource model) :
    Option (List (List RepeatableLevel)) :=
  source.operands.mapM numberEntityOperandReferenceScope?

private def tokenEntityOperandReferenceScope? :
    CheckedTokenEntityOperand model →
      Option (List RepeatableLevel)
  | .field source => some source.declaration.repeatableScope
  | .selected source => some (selectedEntityGuardScope source.source)
  | .star checked => checkedStarBindingScope checked.source
  | .group slot =>
      let scope := slot.source.bindingScope
      if scope.isEmpty then some [] else some scope

private def tokenEntityReferenceScopes?
    (source : CheckedTokenEntitySource model) :
    Option (List (List RepeatableLevel)) :=
  source.operands.mapM tokenEntityOperandReferenceScope?

private def booleanValueCountOperandReferenceScope? :
    CheckedBooleanValueCountOperand model expected →
      Option (List RepeatableLevel)
  | .field source => some source.declaration.repeatableScope
  | .selected source => some (selectedEntityGuardScope source.source)
  | .star source => checkedStarBindingScope source.source
  | .group slot =>
      let scope := slot.source.bindingScope
      if scope.isEmpty then some [] else some scope

private def booleanValueCountReferenceScopes?
    (source : CheckedBooleanValueCountSource model) :
    Option (List (List RepeatableLevel)) :=
  source.operands.mapM booleanValueCountOperandReferenceScope?

private def productReferenceScopes?
    (source : CheckedNumericProductAggregate model) :
    Option (List (List RepeatableLevel)) := do
  match source with
  | .selected source => pure [source.left.source.bindingScopes.flatten,
      source.right.source.bindingScopes.flatten]
  | .row source =>
      let left ← checkedStarBindingScope source.left.source
      let right ← checkedStarBindingScope source.right.source
      pure [left, right]

private structure NumericEntityGuardShape where
  referenceScopes : List (List RepeatableLevel)
  zeroSensitive : Bool
  positiveSensitive : Bool
  rejectsMixedReferences : Bool

/-- The source visitor gives Number entity operations two independent static sensitivities plus an operator-specific rejection of mixed references. The Kernel visitor excludes `SumOfProducts` from its mixed-reference rejection, while preserving its zero sensitivity. -/
private def numericEntityGuardShape? :
    OrderedNumericValidationAtom model →
      Option NumericEntityGuardShape
  | .firstFilled source =>
      (numberEntityReferenceScopes? source).map (⟨·, true, false, true⟩)
  | .valueCount _ source =>
      (numberEntityReferenceScopes? source).map (⟨·, true, true, true⟩)
  | .aggregate op source =>
      (numberEntityReferenceScopes? source).map fun scopes =>
        match op with
        | .sum | .minimum | .maximum => ⟨scopes, true, false, true⟩
        | .distinctCount => ⟨scopes, false, true, true⟩
  | .sumOfProducts source =>
      (productReferenceScopes? source).map (⟨·, true, false, false⟩)
  | .tokenValueCount source =>
      (tokenEntityReferenceScopes? source.source).map (⟨·, true, true, true⟩)
  | .booleanValueCount source =>
      (booleanValueCountReferenceScopes? source).map (⟨·, true, true, true⟩)
  -- The guard shape exists for Number entity operations whose references sit at a queried level.
  -- A group count references groups, not levelled Number entities, so it has no shape here — the
  -- same answer the scalar leaf gives.
  -- The token distinct count shares the Number one's fold, but no measurement crosses that carrier
  -- boundary for the guard, so it classifies nothing and an iterating rule it alone would guard stays
  -- refused as unclassified.
  | .indexed _ | .indexedString _ | .temporalExpression _ | .ordinary _ | .filledGroupCountMixed _ | .filledFieldCount _ | .tokenDistinctCount _
  | .temporalDistinctCount _ => none

private def positiveCountThresholdIsUnguarded
    (entityOnLeft : Bool) : NumericValidationOp → Bool
  | .tolerance _ => true
  | .ordinary comparison =>
      if entityOnLeft then
        match comparison with
        | .less | .lessEqual | .notEqual => true
        | .equal | .greater | .greaterEqual => false
      else
        match comparison with
        | .greater | .greaterEqual | .notEqual => true
        | .equal | .less | .lessEqual => false

private def orderedNumericPlainStarLiteralGuardAt
    (level : RepeatableLevel)
    (comparison : OrderedNumericComparison model) :
    Option IterationGuardStatus :=
  let classify entityExpr literalExpr entityOnLeft := do
    let atom ← match entityExpr with
      | .atom atom => some atom
      | _ => none
    let shape ← numericEntityGuardShape? atom
    match literalExpr with
    | .literal _ =>
        match levelReferenceShapeAt level shape.referenceScopes with
        | .none => some .noReference
        | .mixed => some (if shape.rejectsMixedReferences then .unguarded else .guarded)
        | .allIterating =>
            let literal ← hostConvertedLiteralValue? literalExpr
            if (shape.zeroSensitive && literal == 0 &&
                  directEmptyZeroIsUnguarded comparison.op) ||
                (shape.positiveSensitive && 0 < literal &&
                  positiveCountThresholdIsUnguarded
                    entityOnLeft comparison.op) then
              some .unguarded
            else
              some .guarded
    | _ => none
  match classify comparison.left comparison.right true with
  | some status => some status
  | none => classify comparison.right comparison.left false

/-- Preserve the source visitor's top-level parse-tree distinction: ordinary binary arithmetic and power are composite operations, so the direct field/list-versus-constant branches do not classify them. Grouping retains the underlying operation root. -/
private def isTopLevelCompositeNumericOperation :
    AuthoredNumericExpr Atom → Bool
  | .group body => isTopLevelCompositeNumericOperation body
  | .binary _ _ _ | .power _ _ => true
  | .atom _ | .literal _ | .abs _ | .extremum _ _ _
  | .extremumCall _ _ | .round _ _ _ => false

private def orderedNumericCompositeGuardAt
    (level : RepeatableLevel)
    (comparison : OrderedNumericComparison model) :
    Option IterationGuardStatus :=
  if isTopLevelCompositeNumericOperation comparison.left ||
      isTopLevelCompositeNumericOperation comparison.right then
    match orderedNumericComparisonIterationScope comparison with
    | .ok (some scope) =>
        some (if scope.contains level then .guarded else .noReference)
    | .ok none => some .noReference
    | .error _ => none
  else
    none

def ResolvedGroupListOperands.iterationGuardAt
    (operator : GroupFillQuantifier)
    (operands : List (ResolvedGroupListOperand model))
    (level : RepeatableLevel) : IterationGuardStatus :=
  let references := operands.map fun operand =>
    match ResolvedGroupListOperand.iterationScope operand with
    | some scope => scope.contains level
    | none => false
  if !references.any id then
    .noReference
  else
    match operator with
    | .noGroupFilled => .unguarded
    | .atLeastOneGroupFilled =>
        if references.all id then .guarded else .unguarded
    | .allGroupsFilled | .notAllGroupsFilled
    | .groupsNotCollectivelyFilled => .unclassified

/-- Static wildcard multiplicity is declared capacity, independent of the filter's runtime selection
(IterationNotValidVisitor's entity-list gate; the H10 iteration-guard matrix). Captured reads bind the
rule's row but do not turn its selected wildcard operand into an ordinary row read. -/
private def starIterationExtent? (source : CheckedStarFieldPath model) :
    Option (List RepeatableLevel × Nat) :=
  (model.declarationSlots? source.path.firstStar source.declaration).map (source.bindingScope, ·)

private def fieldFillIterationExtents? (source : CheckedFieldFillList model) :
    Option (List (List RepeatableLevel × Nat)) :=
  source.operands.mapM fun
    | .field declaration => some (declaration.repeatableScope, 1)
    | .star source => starIterationExtent? source.source
    | .indexed _ | .keyed _ | .group _ => none

private def uniquenessIterationExtents? : CheckedValuesNotUniqueCondition model →
    Option (List (List RepeatableLevel × Nat))
  | .number source => source.operands.mapM fun
      | .field source => some (source.declaration.repeatableScope, 1)
      | .star source => starIterationExtent? source.source
      | .starHaving source => starIterationExtent? source.source.source
      | .selected _ | .group _ => none
  | .token source => source.source.operands.mapM fun
      | .field source => some (source.declaration.repeatableScope, 1)
      | .star source => starIterationExtent? source.source
      | .selected _ | .group _ => none
  | .temporal _ => none

private def independentIterationSlots (level : RepeatableLevel)
    (extents : List (List RepeatableLevel × Nat)) : Nat :=
  (extents.map fun (scope, capacity) => if scope.contains level then 0 else capacity).sum

private def fieldFillIterationGuardAt (level : RepeatableLevel) (operator : FieldFillQuantifier)
    (source : CheckedFieldFillList model) : IterationGuardStatus :=
  if !source.bindingScope.contains level then .noReference
  else match fieldFillIterationExtents? source with
    | none => .unclassified
    | some extents =>
        let independent := independentIterationSlots level extents
        let violatesGuard : Bool := match operator with
          | .noFieldFilled | .notAllFieldsFilled | .notExactlyOneFieldFilled =>
              extents.any fun (scope, _) => scope.contains level
          | .atLeastOneFieldFilled | .fieldsNotCollectivelyFilled => 0 < independent
          | .moreThanOneFieldFilled => 1 < independent
          | .allFieldsFilled =>
              match source.operands with
              | [.field _] => 0 < independent
              | _ => false
        if violatesGuard then .unguarded else .guarded

private def uniquenessIterationGuardAt (level : RepeatableLevel)
    (source : CheckedValuesNotUniqueCondition model) : IterationGuardStatus :=
  if !((ordinaryIterationScope (.leaf (.valuesNotUnique source))).toOption.bind id).any (·.contains level) then .noReference
  else match uniquenessIterationExtents? source with
    | none => .unclassified
    | some extents =>
        if 1 < independentIterationSlots level extents then .unguarded else .guarded

private def ValidationConditionLeaf.iterationGuardAt
    (level : RepeatableLevel) :
    ValidationConditionLeaf model → IterationGuardStatus
  | .flat _ | .numeric _ _ | .guardedRootCurrentRepetition _ _ _
  | .customCondition _ => .noReference
  | .customFieldValidity leaf =>
      if leaf.operand.declaration.repeatableScope.contains level then .guarded else .noReference
  | .indexedStringPattern leaf =>
      if leaf.bindingScopes.any (·.contains level) then .guarded else .noReference
  | .indexedCustomFieldValidity leaf =>
      if leaf.source.bindingScopes.any (·.contains level) then .guarded else .noReference
  | .constructedDateValidity operation source =>
      if source.scalarBindingScopes.any (·.contains level) then
        match operation with
        | .valid => .guarded
        | .invalid => .unguarded
      else .noReference
  | .stringPattern leaf =>
      if (model.fieldRepeatableScope leaf.condition.field.id).contains level then .guarded else .noReference
  | .scalarTemporal comparison =>
      if comparison.bindingScopes.any (·.contains level) then .guarded else .noReference
  | .guardedRepeatableCurrentRepetition guard _ _ =>
      if guard.repeatableScope.contains level then .guarded else .noReference
  | .groupList operator operands =>
      ResolvedGroupListOperands.iterationGuardAt operator operands level
  | .fieldFill operator source => fieldFillIterationGuardAt level operator source
  | .stringExpression comparison =>
      if comparison.bindingScopes.any (·.contains level) then .unclassified else .noReference
  | .firstFilledComparison comparison =>
      if comparison.bindingScopes.flatten.contains level then .unclassified else .noReference
  | .tokenComparison comparison =>
      if comparison.bindingScopes.flatten.contains level then .unclassified else .noReference
  | .valueList source =>
      if source.bindingScopes.flatten.contains level then .unclassified else .noReference
  | .valuesNotUnique source => uniquenessIterationGuardAt level source
  | .orderedNumeric _ comparison =>
      match orderedNumericCompositeGuardAt level comparison with
      | some status => status
      | none =>
          match orderedNumericPlainStarLiteralGuardAt level comparison with
          | some status => status
          | none =>
              match orderedNumericDirectWrapperLiteralGuardAt level comparison with
              | some status => status
              | none =>
                  match orderedNumericDirectFieldLiteralGuardAt level comparison with
                  | some status => status
                  | none =>
                      match orderedNumericComparisonIterationScope comparison with
                      | .ok (some scope) =>
                          if scope.contains level then .unclassified else .noReference
                      | .ok none => .noReference
                      | .error _ => .unclassified
  | .groupPresence operator reference =>
      if (model.repeatableScopeForGroupPath reference.path).contains level then
        match operator with
        | .filled => .guarded
        | .notFilled => .unguarded
      else
        .noReference
  | .keyedGroupPresence _ _ | .indexedFieldPresence _ _ => .noReference
  | .repeatableFieldPresence operator declaration =>
      if declaration.repeatableScope.contains level then
        match operator with
        | .filled => .guarded
        | .notFilled => .unguarded
      else
        .noReference
  | .repetitionNotUnique source =>
      if (source.topology.path.axes.map (·.level)).contains level then
        .guarded
      else
        .noReference
  | .iteratedDateRange condition =>
      -- A value comparison guards its own level at every polarity. The Kernel refuses a negated
      -- *presence* leaf at an iterated level, and the same model admits `==`, `!=`, and the order
      -- operators on a repeatable operand, so polarity is not this leaf's question.
      if condition.bindingScopes.any (·.contains level) then
        .guarded
      else
        .noReference

def iterationGuardStatusAt (condition : ValidationCondition model)
    (level : RepeatableLevel) : IterationGuardStatus :=
  condition.iterationGuardStatus
    (ValidationConditionLeaf.iterationGuardAt level)

private def iterationLegalityForLevels
    (condition : ValidationCondition model) :
    List RepeatableLevel → IterationLegality
  | [] => .legal
  | level :: remaining =>
      match condition.iterationGuardStatusAt level with
      | .guarded => iterationLegalityForLevels condition remaining
      | .unguarded => .invalid level
      | .noReference | .unclassified => .insufficient level

/-- Analyze the levels already derived from the complete checked condition, outermost first. Scope incompatibility remains the existing separate assembly error. -/
def iterationLegality (condition : ValidationCondition model) :
    Except RuleIterationScopeError IterationLegality := do
  match ← condition.ordinaryIterationScope with
  | none => pure .legal
  | some scope => pure (iterationLegalityForLevels condition scope)

/-- Ordinary repeatable Number declarations retained by one ordered expression in authored order. -/
private def ordinaryNumericAtomRepeatableFields
    (model : FlatModel) :
    OrderedNumericValidationAtom model → List FlatFieldDecl
  | .ordinary source =>
      match ordinaryNumericAtomFieldDeclarations? model source with
      | none => []
      | some declarations =>
          declarations.filter fun declaration =>
            !declaration.repeatableScope.isEmpty
  | _ => []

private def authoredNumericRepeatableFields
    (fieldsOf : Atom → List FlatFieldDecl) :
    AuthoredNumericExpr Atom → List FlatFieldDecl
  | .atom atom => fieldsOf atom
  | .literal _ => []
  | .group body | .abs body | .extremumCall _ body | .round _ _ body =>
      authoredNumericRepeatableFields fieldsOf body
  | .binary _ left right | .power left right | .extremum _ left right =>
      authoredNumericRepeatableFields fieldsOf left ++
        authoredNumericRepeatableFields fieldsOf right

/-- Ordinary repeatable field declarations in authored tree order. Whole-rule checked-document execution resolves these exact cells before evaluation so a structural address failure cannot be collapsed into semantic UNKNOWN. -/
def ordinaryRepeatableFields (condition : ValidationCondition model) :
    List FlatFieldDecl :=
  match condition with
  | .leaf (.repeatableFieldPresence _ declaration) => [declaration]
  | .leaf (.constructedDateValidity _ source) =>
      source.scalarBoundFieldIds.filterMap fun field =>
        (model.lookupUniqueId field).toOption.filter (fun declaration => !declaration.repeatableScope.isEmpty)
  | .leaf (.stringExpression comparison) =>
      comparison.boundDeclarations.filter fun field => !field.repeatableScope.isEmpty
  | .leaf (.scalarTemporal comparison) =>
      (comparison.left.boundFieldIds ++ comparison.right.boundFieldIds).filterMap fun field =>
        (model.lookupUniqueId field).toOption.filter (fun declaration => !declaration.repeatableScope.isEmpty)
  | .leaf (.orderedNumeric _ comparison) =>
      authoredNumericRepeatableFields
          (ordinaryNumericAtomRepeatableFields model) comparison.left ++
        authoredNumericRepeatableFields
          (ordinaryNumericAtomRepeatableFields model) comparison.right
  | .leaf (.repetitionNotUnique source) =>
      source.keys.map fun key => key.source.declaration
  | .leaf (.guardedRepeatableCurrentRepetition guard _ _) => [guard]
  | .leaf (.iteratedDateRange condition) =>
      condition.repeatableDeclarations
  | .leaf _ => []
  | .and left right | .or left right =>
      ordinaryRepeatableFields left ++ ordinaryRepeatableFields right

/-- Whether every leaf can consume the complete environment selected by ordinary nonparallel rule iteration. Specialized star sources remain with their family owners. -/
def supportsOrdinaryIteration
    (condition : ValidationCondition model) : Bool :=
  condition.allLeaves fun
    | .flat _ | .groupPresence _ _ | .groupList _ _
    | .keyedGroupPresence _ _ | .indexedFieldPresence _ _ | .repeatableFieldPresence _ _
    | .guardedRootCurrentRepetition _ _ _ => true
    | .guardedRepeatableCurrentRepetition _ _ _ => true
    | .iteratedDateRange _ => true
    | .orderedNumeric .sameGroupAddressed _ => true
    | .repetitionNotUnique _ => true
    | .customCondition _ | .constructedDateValidity _ _ | .customFieldValidity _ | .indexedCustomFieldValidity _ => true
    | .stringPattern _ | .indexedStringPattern _ => true
    | .stringExpression _ | .scalarTemporal _ | .firstFilledComparison _ | .tokenComparison _ | .fieldFill _ _ | .valueList _ | .valuesNotUnique _ => true
    | _ => false

/-- Discover a filtered source across the complete checked connective tree. Unlike verdict evaluation, this static traversal never short-circuits on a decisive branch. -/
def hasHaving (condition : ValidationCondition model) : Bool :=
  condition.anyLeaf ValidationConditionLeaf.hasHaving

/-- Public execution-mode query for checked consumers. A true result requires the full addressed evaluator; choosing the scalar route is an explicit context error rather than semantic UNKNOWN. -/
def requiresAddressedValidation
    (condition : ValidationCondition model) : Bool :=
  condition.anyLeaf ValidationConditionLeaf.requiresAddressedValidation

def wellFormedBool (condition : ValidationCondition model)
    (rowGroup : GroupPath) (declaringGroup : GroupPath := rowGroup) : Bool :=
  condition.repetitionNotUniqueSources.length < 2 &&
    condition.allLeaves fun leaf => leaf.wellFormedBool rowGroup declaringGroup

/-- Reached temporal runtime failure aborts the enclosing rule, rather than entering the
truth algebra as an ordinary fired leaf (temporal review grid, 2026-10-03). Structural failures
remain in the caller's error domain. -/
def evalWithTemporalResult (condition : ValidationCondition model)
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance)
    (evaluate : ValidationConditionLeaf model → Except Error Verdict)
    (onTemporalUnavailable : Except Error Verdict := .ok .unknown)
    (temporalFields : CheckedScalarTemporalComparison model → Except Error FlatContext :=
      fun _ => pure context.fields)
    (onTemporalValueFailure : ScalarTemporalEvaluationFault → Except Error Verdict :=
      fun _ => .ok (.fired .value))
    (numericResult : OrderedNumericComparison model → Except (Sum Error ScalarTemporalEvaluationFault) Verdict :=
      fun comparison => (comparison.evalSelectedResult context isRelevant).mapError Sum.inr)
    (leafRuntimeFault? : Error → Option ScalarTemporalEvaluationFault := fun _ => none)
    (firstFilledResult : CheckedFirstFilledComparison model → Except (Sum Error ScalarTemporalEvaluationFault) Verdict :=
      fun _ => pure .unknown)
    (customResult : String → Except Error Verdict := fun name =>
      pure ((context.customResult name).toOption.getD .unknown))
    (temporalAddressed : CheckedScalarTemporalComparison model → Except Error (Option ComputationFillContext × Env) :=
      fun _ => pure (none, []))
    (temporalPartialResult? : ValidationConditionLeaf model → Option (Except (Sum Error ScalarTemporalEvaluationFault) Verdict) :=
      fun _ => none) :
    Except Error Verdict :=
  let readLeaf : ValidationConditionLeaf model → Except (Sum Error ScalarTemporalEvaluationFault) Verdict :=
    fun leaf => match temporalPartialResult? leaf with
      | some result => result
      | none => match leaf with
        | .customCondition name => (customResult name.value).mapError Sum.inl
        | .firstFilledComparison comparison => firstFilledResult comparison
        | .scalarTemporal comparison =>
            if comparison.fieldIds.all isRelevant then do
              let fields ← (temporalFields comparison).mapError Sum.inl
              let (addressed, row) ← (temporalAddressed comparison).mapError Sum.inl
              (comparison.evalResult .validation fields addressed row).mapError Sum.inr
            else pure .unknown
        | leaf@(.orderedNumeric _ comparison) =>
            if comparison.hasTemporalExpression then numericResult comparison
            else (evaluate leaf).mapError Sum.inl
        | leaf => (evaluate leaf).mapError Sum.inl
  let readLeaf := fun leaf => (readLeaf leaf).mapError fun
    | .inl error => match leafRuntimeFault? error with
        | some fault => .inr fault
        | none => .inl error
    | .inr fault => .inr fault
  let hasCustom := condition.anyLeaf fun | .customCondition _ => true | _ => false
  let result : Except (Sum Error ScalarTemporalEvaluationFault) Verdict :=
    if hasCustom then condition.evalObservedM
      (condition.anyLeaf ValidationConditionLeaf.requiresClassificationPass) readLeaf
    else match condition with
    | .leaf leaf => readLeaf leaf
    | _ => do
      let holds ← condition.evalBoolExcept fun leaf => do
        pure (match ← readLeaf leaf with | .fired _ => true | _ => false)
      if holds then
        if condition.anyLeaf ValidationConditionLeaf.requiresClassificationPass then
          condition.evalClassificationExcept readLeaf
        else condition.evalVerdictExcept readLeaf
      else
        -- Non-firing still retains the theory's UNKNOWN distinction. This projection cannot raise
        -- a runtime failure the generated Boolean pass has already skipped; context faults remain
        -- explicit. `CodeGenRuleDefinition.st` enters classification only after a true condition.
        condition.evalVerdictExcept fun leaf =>
          match readLeaf leaf with
          | .error (.inr .dateTimeLabelUnresolved) | .error (.inr .componentNumberInvalid)
          | .error (.inr (.addressing .typeValidityValueFailure)) => .ok .unknown
          | result => result
  match result with
  | .ok verdict => .ok verdict
  | .error (.inl error) => .error error
  | .error (.inr fault@(.dateTimeLabelUnresolved))
  | .error (.inr fault@(.componentNumberInvalid))
  | .error (.inr fault@(.addressing .typeValidityValueFailure)) => onTemporalValueFailure fault
  | .error (.inr .calendarUnavailable) | .error (.inr .indexedOperandNotSupported)
  | .error (.inr (.addressing _)) => onTemporalUnavailable

/-- Evaluate one mixed tree with the rule-owned truth and classification phases. -/
def evalSelected (condition : ValidationCondition model)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance := fun _ => true) : Verdict :=
  match condition.evalWithTemporalResult context isRelevant
      (fun leaf => Except.ok (ε := Empty) (leaf.evalSelected context isRelevant))
      (temporalPartialResult? := fun
        | .customFieldValidity leaf => some do
            if !isRelevant leaf.operand.source then return .unknown
            (leaf.evalValidationObservation (observeCell .validation
              (context.fields.read leaf.operand.source))).mapError
                (fun _ => .inr (.addressing .typeValidityValueFailure))
        | _ => none) with
  | .ok verdict => verdict
  | .error impossible => nomatch impossible

/-- Apply the ordinary full-validation content gate to a mixed resolved tree. -/
def evalFull (condition : ValidationCondition model)
    (context : ValidationEvaluationContext)
    (hasContent : Bool) : Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalSelected context
  else .notFired

/-- Bind only a reached temporal leaf to exact row cells; the row-binding grid separates this view from the scalar context without changing the temporal evaluator. -/
private def addressedTemporalFields (context : AddressedValidationEvaluationContext model)
    (comparison : CheckedScalarTemporalComparison model) : Except CheckedAddressingError FlatContext := do
  for scope in comparison.bindingScopes do
    discard <| (context.outer.pathForScope scope).mapError CheckedAddressingError.environment
  let fields := comparison.fieldIds.filter fun field =>
    (context.outer.pathForScope (model.fieldRepeatableScope field)).isOk
  let cells ← fields.mapM fun field => do
    pure (field, ← context.readCell context.outer field)
  let storedText ← match context.input with
    | .checked document | .partialView document _ => pure (document.storedTextIn context.outer)
    | .legacy _ _ => do
        let rawFields := comparison.left.storedTextFields ++ comparison.right.storedTextFields
        if rawFields.any (fun field => (model.lookupUniqueId field).toOption.any
            (fun declaration => !declaration.repeatableScope.isEmpty)) then
          throw (.checkedDocumentRequired [])
        pure context.scalar.fields.storedText
  pure { context.scalar.fields with
    storedText
    read := fun field => ((cells.find? (·.1 == field)).map (·.2)).getD malformedCheckedCell }

private def addressedTemporalContext (context : AddressedValidationEvaluationContext model)
    (comparison : CheckedScalarTemporalComparison model) :
    Except CheckedAddressingError (Option ComputationFillContext × Env) := do
  if !comparison.left.requiresAddressed && !comparison.right.requiresAddressed then return (none, context.outer)
  match context.input with
  | .checked document => pure (some document.indexedComputationFillContext, context.outer)
  | .legacy _ _ | .partialView _ _ => throw (.checkedDocumentRequired [])

/-- A legal extensible String can fail numeric conversion at runtime; the generated rule
handler catches that failure outside the Boolean tree (spec/05 §3), unlike a missing host input. -/
def addressedValueFailure? : CheckedAddressingError → Option ScalarTemporalEvaluationFault
  | .constructedDate (.stringNotConvertible _ _) => some .componentNumberInvalid
  | .temporalValueFailure => some .dateTimeLabelUnresolved
  | .typeValidityValueFailure => some (.addressing .typeValidityValueFailure)
  | _ => none

/-- Evaluate one row-selected checked tree while retaining structural addressing failure outside the verdict algebra. Truth testing and conditional classification retain their separate failure boundaries. -/
def evalAddressed (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError Verdict :=
  condition.evalWithTemporalResult context.scalar context.directRelevant
    (fun leaf => leaf.evalAddressed context) (.error .temporalUnavailable)
    (addressedTemporalFields context)
    (temporalAddressed := addressedTemporalContext context)
    (numericResult := fun comparison => comparison.evalAddressedResult context)
    (leafRuntimeFault? := addressedValueFailure?)
    (firstFilledResult := ValidationConditionLeaf.evalFirstFilledComparisonAddressedResult context)
    (customResult := fun name => (context.scalar.customResult name).mapError CheckedAddressingError.customCondition)

/-- Evaluate the same connective tree with one already-prepared current-row RNU result. Duplicate construction remains outside and branch-independent. -/
def evalAddressedWithRepetitionNotUnique
    (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (result? : Option RepetitionNotUniqueResult) :
    Except CheckedAddressingError Verdict :=
  condition.evalWithTemporalResult context.scalar context.directRelevant
    (fun leaf => leaf.evalAddressedWithRepetitionNotUnique context result?) (.error .temporalUnavailable)
    (addressedTemporalFields context)
    (temporalAddressed := addressedTemporalContext context)
    (numericResult := fun comparison => comparison.evalAddressedResult context)
    (leafRuntimeFault? := addressedValueFailure?)
    (firstFilledResult := ValidationConditionLeaf.evalFirstFilledComparisonAddressedResult context)
    (customResult := fun name => (context.scalar.customResult name).mapError CheckedAddressingError.customCondition)

/-- Keep reached temporal failure distinct from a row verdict until the rule's iteration handler.
The generated Java `CodeGenRuleDefinition.st` catches outside its row loop. -/
def evalAddressedWithRepetitionNotUniqueResult
    (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (result? : Option RepetitionNotUniqueResult) :
    Except (Sum CheckedAddressingError ScalarTemporalEvaluationFault) Verdict :=
  condition.evalWithTemporalResult context.scalar context.directRelevant
    (fun leaf => (leaf.evalAddressedWithRepetitionNotUnique context result?).mapError Sum.inl)
    (.error (.inl .temporalUnavailable))
    (fun comparison => (addressedTemporalFields context comparison).mapError Sum.inl)
    (fun fault => .error (.inr fault))
    (temporalAddressed := fun comparison => (addressedTemporalContext context comparison).mapError Sum.inl)
    (numericResult := fun comparison => (comparison.evalAddressedResult context).mapError fun
      | .inl error => .inl (.inl error)
      | .inr fault => .inr fault)
    (leafRuntimeFault? := fun
      | .inl error => addressedValueFailure? error
      | .inr fault => some fault)
    (firstFilledResult := fun comparison =>
      (ValidationConditionLeaf.evalFirstFilledComparisonAddressedResult context comparison).mapError fun
        | .inl error => .inl (.inl error)
        | .inr fault => .inr fault)
    (customResult := fun name => (context.scalar.customResult name).mapError
      (fun error => .inl (.customCondition error)))

/-- Apply the ordinary full-validation content gate to the addressed tree without sampling any repeatable source on an ineligible empty row. -/
def evalAddressedFull (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) : Except CheckedAddressingError Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalAddressed context
  else pure .notFired

/-- Apply the ordinary content gate before the RNU-aware addressed connective walk. -/
def evalAddressedFullWithRepetitionNotUnique
    (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) (result? : Option RepetitionNotUniqueResult) :
    Except CheckedAddressingError Verdict :=
  if hasContent || condition.canFireOnEmpty then
    condition.evalAddressedWithRepetitionNotUnique context result?
  else
    pure .notFired

end ValidationCondition

end A12Kernel
