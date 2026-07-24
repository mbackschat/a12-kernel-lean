import A12Kernel.Elaboration.ValidationCondition.Core

/-! # Validation-condition iteration legality and addressed execution -/

namespace A12Kernel

namespace DecodedNumericLiteral

private def pow2Rat (exponent : Int) : Rat :=
  if 0 ≤ exponent then
    (2 ^ exponent.toNat : Nat)
  else
    1 / (2 ^ (-exponent).toNat : Nat)

private def roundNonnegativeTiesEven (value : Rat) : Nat :=
  let numerator := value.num.toNat
  let denominator := value.den
  let quotient := numerator / denominator
  let remainder := numerator % denominator
  if 2 * remainder < denominator then
    quotient
  else if denominator < 2 * remainder then
    quotient + 1
  else if quotient % 2 == 0 then
    quotient
  else
    quotient + 1

private def floorLog2Positive (value : Rat) : Int :=
  let estimate :=
    Int.ofNat value.num.toNat.log2 - Int.ofNat value.den.log2
  if value < pow2Rat estimate then estimate - 1 else estimate

/-- Round one nonzero finite rational to the nearest IEEE-754 binary64 value, with ties to an even significand. Callers bound the magnitude below `2^63`, so overflow and infinities cannot arise here. -/
private def roundToBinary64 (value : Rat) : Rat :=
  let negative := value < 0
  let magnitude := if negative then -value else value
  let exponent := floorLog2Positive magnitude
  let stepExponent :=
    if magnitude < pow2Rat (-1022) then -1074 else exponent - 52
  let step := pow2Rat stepExponent
  let units := roundNonnegativeTiesEven (magnitude / step)
  let rounded := (units : Rat) * step
  if negative then -rounded else rounded

private def javaRoundedLong (value : Rat) : Int :=
  let longLimit : Rat := 2 ^ 63
  if longLimit ≤ value then
    9223372036854775807
  else if value ≤ -longLimit then
    -9223372036854775808
  else
    let binary64 := if value == 0 then 0 else roundToBinary64 value
    let rounded := (binary64 + 1 / 2).floor
    if (9223372036854775807 : Int) < rounded then
      9223372036854775807
    else if rounded < (-9223372036854775808 : Int) then
      -9223372036854775808
    else
      rounded

private def narrowSignedInt32 (value : Int) : Int :=
  let residue := value.emod 4294967296
  if residue < 2147483648 then residue else residue - 4294967296

/-- Reproduce the parser visitor's `Double.parseDouble` → `Math.round` → Java signed-`int` narrowing for one checked finite-decimal literal. Exact rational value plus authored scale is sufficient because the grammar admits no exponent and preserves every fractional digit; values that are not representable by that checked decimal shape remain explicit insufficiency. -/
def iterationHostInt32? (literal : DecodedNumericLiteral) : Option Int :=
  if literal.authoredScale < 0 then
    none
  else if (literal.value *
      (10 ^ literal.authoredScale.toNat : Nat)).den != 1 then
    none
  else
    some (narrowSignedInt32 (javaRoundedLong literal.value))

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

private def numberEntityOperandReferenceScope? :
    CheckedNumberEntityOperand model →
      Option (List RepeatableLevel)
  | .field _ => some []
  | .star checked => checkedStarBindingScope checked.source
  | .starHaving checked => checkedStarBindingScope checked.source.source

private def numberEntityReferenceScopes?
    (source : CheckedNumberEntitySource model) :
    Option (List (List RepeatableLevel)) :=
  source.operands.mapM numberEntityOperandReferenceScope?

private def tokenEntityOperandReferenceScope? :
    CheckedTokenEntityOperand model →
      Option (List RepeatableLevel)
  | .field _ => some []
  | .star checked => checkedStarBindingScope checked.source

private def tokenEntityReferenceScopes?
    (source : CheckedTokenEntitySource model) :
    Option (List (List RepeatableLevel)) :=
  source.operands.mapM tokenEntityOperandReferenceScope?

private def productReferenceScopes?
    (source : CheckedNumericProductAggregate model) :
    Option (List (List RepeatableLevel)) := do
  let left ← checkedStarBindingScope source.left.source
  let right ← checkedStarBindingScope source.right.source
  pure [left, right]

private structure NumericEntityGuardShape where
  referenceScopes : List (List RepeatableLevel)
  zeroSensitive : Bool
  positiveSensitive : Bool

/-- The source visitor gives Number entity operations two independent static sensitivities plus a stronger any-constant rejection when their references mix at the queried level. -/
private def numericEntityGuardShape? :
    OrderedNumericValidationAtom model →
      Option NumericEntityGuardShape
  | .firstFilled source =>
      (numberEntityReferenceScopes? source).map (⟨·, true, false⟩)
  | .valueCount _ source =>
      (numberEntityReferenceScopes? source).map (⟨·, true, true⟩)
  | .aggregate op source =>
      (numberEntityReferenceScopes? source).map fun scopes =>
        match op with
        | .sum | .minimum | .maximum => ⟨scopes, true, false⟩
        | .distinctCount => ⟨scopes, false, true⟩
  | .sumOfProducts source =>
      (productReferenceScopes? source).map (⟨·, true, false⟩)
  | .tokenValueCount source =>
      (tokenEntityReferenceScopes? source.source).map (⟨·, true, true⟩)
  | .ordinary _ => none

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
        | .mixed => some .unguarded
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

private def ValidationConditionLeaf.iterationGuardAt
    (level : RepeatableLevel) :
    ValidationConditionLeaf model → IterationGuardStatus
  | .flat _ | .numeric _ _ | .groupList _ _ => .noReference
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
  | .leaf (.orderedNumeric _ comparison) =>
      authoredNumericRepeatableFields
          (ordinaryNumericAtomRepeatableFields model) comparison.left ++
        authoredNumericRepeatableFields
          (ordinaryNumericAtomRepeatableFields model) comparison.right
  | .leaf (.repetitionNotUnique source) =>
      source.keys.map fun key => key.source.declaration
  | .leaf _ => []
  | .and left right | .or left right =>
      ordinaryRepeatableFields left ++ ordinaryRepeatableFields right

/-- The first whole-rule route accepts established nonrepeatable flat leaves, ordinary repeatable field/group presence, and the checked same-group addressed Number policy. Specialized star sources retain their existing owners until their rule-environment bridge closes. -/
def supportsOrdinaryIteration
    (condition : ValidationCondition model) : Bool :=
  condition.allLeaves fun
    | .flat _ | .groupPresence _ _ | .repeatableFieldPresence _ _ => true
    | .orderedNumeric .sameGroupAddressed _ => true
    | .repetitionNotUnique source => source.supportsOneLevelOrdinaryRule
    | _ => false

/-- Discover a filtered source across the complete checked connective tree. Unlike verdict evaluation, this static traversal never short-circuits on a decisive branch. -/
def hasHaving (condition : ValidationCondition model) : Bool :=
  condition.anyLeaf ValidationConditionLeaf.hasHaving

/-- Public execution-mode query for checked consumers. A true result requires the full addressed evaluator; choosing the scalar route is an explicit context error rather than semantic UNKNOWN. -/
def requiresAddressedValidation
    (condition : ValidationCondition model) : Bool :=
  condition.anyLeaf ValidationConditionLeaf.requiresAddressedValidation

def wellFormedBool (condition : ValidationCondition model)
    (rowGroup : GroupPath) : Bool :=
  condition.repetitionNotUniqueSources.length < 2 &&
    condition.allLeaves fun leaf => leaf.wellFormedBool rowGroup

/-- Evaluate a row-selected mixed tree through the sole connective evaluator. -/
def evalSelected (condition : ValidationCondition model)
    (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance := fun _ => true) : Verdict :=
  condition.evalVerdict fun leaf => leaf.evalSelected context isRelevant

/-- Apply the ordinary full-validation content gate to a mixed resolved tree. -/
def evalFull (condition : ValidationCondition model)
    (context : ValidationEvaluationContext)
    (hasContent : Bool) : Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalSelected context
  else .notFired

/-- Evaluate one row-selected checked tree while retaining structural addressing failure outside the verdict algebra. The generic effectful connective fold preserves the ordinary decisive-left short-circuit boundary. -/
def evalAddressed (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model) :
    Except CheckedAddressingError Verdict :=
  condition.evalVerdictExcept fun leaf => leaf.evalAddressed context

/-- Evaluate the same connective tree with one already-prepared current-row RNU result. Duplicate construction remains outside and branch-independent. -/
def evalAddressedWithRepetitionNotUnique
    (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (result? : Option RepetitionNotUniqueResult) :
    Except CheckedAddressingError Verdict :=
  condition.evalVerdictExcept fun leaf =>
    leaf.evalAddressedWithRepetitionNotUnique context result?

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
