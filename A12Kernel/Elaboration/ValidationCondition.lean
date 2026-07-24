import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.ValidationContext

/-! # Shared resolved validation conditions

This boundary joins the established flat leaves and resolved numeric-expression comparisons under one connective tree. It deliberately begins after each leaf family's checked elaboration; a later checked whole-rule capsule must preserve those certificates rather than accepting forged cores.
-/

namespace A12Kernel

/-- One authored operand of the kernel's fixed group-list condition family. Despite the language-level name, the checked entity list admits both fields and groups. Starred group scopes remain a separate SG2 source shape. -/
inductive SurfaceGroupListOperand where
  | field (reference : SurfaceFieldPath)
  | group (reference : SurfaceGroupReference)
  deriving Repr, DecidableEq

/-- A fixed group-list operand after model-owned field/group resolution. A field retains its exact declaration so overlap and checked-core coherence cannot be forged from an ID alone. -/
inductive ResolvedGroupListOperand where
  | field (declaration : FlatFieldDecl)
  | group (reference : ResolvedGroupReference)
  deriving Repr, DecidableEq

/-- Presence operators for an ordinary non-starred repeatable field reference. Evaluation reuses the established scalar presence observation after the rule environment has selected one exact field instance. -/
inductive RepeatableFieldPresenceOperator where
  | filled
  | notFilled
  deriving Repr, DecidableEq

namespace RepeatableFieldPresenceOperator

def canFireOnEmpty : RepeatableFieldPresenceOperator → Bool
  | .filled => false
  | .notFilled => true

def eval (operator : RepeatableFieldPresenceOperator)
    (observation : CellObservation) : Verdict :=
  match operator with
  | .filled => observation.evalValidationFilled
  | .notFilled => observation.evalValidationNotFilled

end RepeatableFieldPresenceOperator

namespace ResolvedGroupListOperand

def entityPath : ResolvedGroupListOperand → List String
  | .field declaration => declaration.path
  | .group reference => reference.path

def isRootGroup : ResolvedGroupListOperand → Bool
  | .field _ => false
  | .group reference => reference.isRoot

def referencesField (operand : ResolvedGroupListOperand)
    (model : FlatModel) (field : FieldId) : Bool :=
  match operand with
  | .field declaration => declaration.id == field
  | .group reference => reference.referencesField model field

def wellFormedBool (operand : ResolvedGroupListOperand)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  match operand with
  | .field declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok checked =>
          checked == declaration && declaration.repeatableScope.isEmpty
      | .error _ => false
  | .group reference =>
      reference.fixedWellFormedBool model rowGroup

/-- Kernel entity-list duplicate checking rejects direct duplicates and every group/descendant pair. Sibling fields and sibling groups remain independent. -/
def overlaps (left right : ResolvedGroupListOperand) : Bool :=
  match left, right with
  | .field leftDeclaration, .field rightDeclaration =>
      leftDeclaration.id == rightDeclaration.id
  | .group leftReference, .group rightReference =>
      leftReference.overlaps rightReference
  | .group reference, .field declaration
  | .field declaration, .group reference =>
      reference.path.isPrefixOf declaration.groupPath

end ResolvedGroupListOperand

namespace ResolvedGroupListOperands

def firstOverlap? : List ResolvedGroupListOperand →
    Option (List String × List String)
  | [] => none
  | first :: rest =>
      match rest.find? (first.overlaps ·) with
      | some overlapping => some (first.entityPath, overlapping.entityPath)
      | none => firstOverlap? rest

def wellFormedBool (operands : List ResolvedGroupListOperand)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  !operands.isEmpty &&
    1 < operands.length &&
    operands.all (·.wellFormedBool model rowGroup) &&
    (firstOverlap? operands).isNone &&
    !operands.any ResolvedGroupListOperand.isRootGroup

end ResolvedGroupListOperands

/-- Static contribution of one checked condition subtree at one repeatable level. `unclassified` means the subtree references that level but its operator-specific guard rule has not yet been established. -/
inductive IterationGuardStatus where
  | noReference
  | unguarded
  | guarded
  | unclassified
  deriving Repr, DecidableEq

namespace IterationGuardStatus

/-- An `And` is guarded when either referenced conjunct supplies a known guard. An unclassified referenced conjunct matters only when no sibling already guards the level. -/
def and : IterationGuardStatus → IterationGuardStatus → IterationGuardStatus
  | .guarded, _ | _, .guarded => .guarded
  | .unclassified, _ | _, .unclassified => .unclassified
  | .unguarded, _ | _, .unguarded => .unguarded
  | .noReference, .noReference => .noReference

/-- Every `Or` branch must reference and guard the level. A missing or known-unguarded branch decides failure; an unclassified branch remains explicit only when every other branch is guarded. -/
def or : IterationGuardStatus → IterationGuardStatus → IterationGuardStatus
  | .guarded, .guarded => .guarded
  | .unclassified, .guarded
  | .guarded, .unclassified
  | .unclassified, .unclassified => .unclassified
  | .noReference, .noReference => .noReference
  | _, _ => .unguarded

end IterationGuardStatus

namespace ConditionTree

/-- Fold per-leaf static iteration guards through the kernel's level-local `And`/`Or` admission algebra. -/
def iterationGuardStatus (classify : Leaf → IterationGuardStatus) :
    ConditionTree Leaf → IterationGuardStatus
  | .leaf value => classify value
  | .and left right =>
      IterationGuardStatus.and
        (left.iterationGuardStatus classify)
        (right.iterationGuardStatus classify)
  | .or left right =>
      IterationGuardStatus.or
        (left.iterationGuardStatus classify)
        (right.iterationGuardStatus classify)

end ConditionTree

/-- The currently resolved validation leaf families, indexed by the one checked model that owns every retained source certificate. -/
inductive ValidationConditionLeaf (model : FlatModel) where
  | flat (condition : FlatConditionLeaf)
  | numeric (scope : NumericOperandScope) (comparison : NumericComparison)
  | orderedNumeric (scope : NumericOperandScope)
      (comparison : OrderedNumericComparison model)
  | groupPresence (operator : GroupPresenceOperator)
      (reference : ResolvedGroupReference)
  | groupList (operator : GroupFillQuantifier)
      (operands : List ResolvedGroupListOperand)
  | repeatableFieldPresence (operator : RepeatableFieldPresenceOperator)
      (declaration : FlatFieldDecl)

/-- One connective tree whose leaves may be ordinary flat clauses or model-certified resolved numeric-expression comparisons. -/
abbrev ValidationCondition (model : FlatModel) :=
  ConditionTree (ValidationConditionLeaf model)

namespace ValidationCondition

/-- Embed an established flat tree without retaining a nested connective tree. -/
def flat (condition : FlatCondition) : ValidationCondition model :=
  condition.map .flat

/-- Admit one resolved numeric comparison as a leaf. Checked construction remains with `CheckedNumericComparison`. -/
def numeric (comparison : NumericComparison) : ValidationCondition model :=
  .leaf (.numeric .sameGroup comparison)

/-- Preserve the checked operand policy when embedding a numeric comparison. -/
def numericIn (scope : NumericOperandScope)
    (comparison : NumericComparison) : ValidationCondition model :=
  .leaf (.numeric scope comparison)

/-- Embed a numeric comparison whose checked atoms own relevance timing. -/
def orderedNumericIn (scope : NumericOperandScope)
    (comparison : OrderedNumericComparison model) : ValidationCondition model :=
  .leaf (.orderedNumeric scope comparison)

/-- Embed one resolved scalar group-presence predicate without re-traversing document state. -/
def groupPresence (operator : GroupPresenceOperator)
    (reference : ResolvedGroupReference) : ValidationCondition model :=
  .leaf (.groupPresence operator reference)

/-- Embed one fixed checked field/group presence list without expanding it into a parallel connective tree. -/
def groupList (operator : GroupFillQuantifier)
    (operands : List ResolvedGroupListOperand) : ValidationCondition model :=
  .leaf (.groupList operator operands)

/-- Embed one ordinary non-starred repeatable field presence reference. Checked construction retains the exact model declaration; whole-rule assembly derives iteration from this leaf rather than accepting caller-supplied scope metadata. -/
def repeatableFieldPresence (operator : RepeatableFieldPresenceOperator)
    (declaration : FlatFieldDecl) : ValidationCondition model :=
  .leaf (.repeatableFieldPresence operator declaration)

end ValidationCondition

namespace ResolvedGroupReference

/-- A group-presence leaf retains one known ordinary group path or the exact declaring `RuleGroup`. Whether it needs a row environment is derived separately from the resolved path's repeatable scope. -/
def presenceWellFormedBool (reference : ResolvedGroupReference)
    (model : FlatModel) (rowGroup : GroupPath) : Bool :=
  model.hasGroupPath reference.path &&
    match reference.origin with
    | .path => true
    | .ruleGroup => reference.path == rowGroup

end ResolvedGroupReference

def ResolvedGroupListOperand.evalPresence
    (context : ValidationEvaluationContext) (isRelevant : FlatRelevance) :
    ResolvedGroupListOperand → GroupListPresenceState
  | .field declaration =>
      if isRelevant declaration.id then
        (declaration.toPresenceField.observeValidation context.fields).asGroupListPresence
      else
        .unavailable
  | .group reference =>
      match context.groups reference.path with
      | some state => state.asGroupListPresence
      | none => .unavailable

namespace ValidationConditionLeaf

def canFireOnEmpty : ValidationConditionLeaf model → Bool
  | .flat condition => condition.canFireOnEmpty
  | .numeric _ _ | .orderedNumeric _ _ => false
  | .groupPresence operator _ => operator.canFireOnEmpty
  | .groupList operator _ => operator.canFireOnEmpty
  | .repeatableFieldPresence operator _ => operator.canFireOnEmpty

def referencesField : ValidationConditionLeaf model → FieldId → Bool
  | .flat condition, field => condition.referencesField field
  | .numeric _ comparison, field => comparison.referencesField model field
  | .orderedNumeric _ comparison, field =>
      comparison.referencesField field
  | .groupPresence _ reference, field => reference.referencesField model field
  | .groupList _ operands, field =>
      operands.any fun operand => operand.referencesField model field
  | .repeatableFieldPresence _ declaration, field =>
      declaration.id == field

/-- Whether a leaf retains any `Having` filter in its checked source. Only the model-indexed ordered numeric carrier can currently own such a source; scalar leaves cannot manufacture the marker. -/
def hasHaving : ValidationConditionLeaf model → Bool
  | .orderedNumeric _ comparison => comparison.hasHaving
  | .flat _ | .numeric _ _ | .groupPresence _ _ | .groupList _ _
  | .repeatableFieldPresence _ _ => false

/-- Whether this leaf retains a repeatable numeric source and therefore cannot use the scalar checked evaluator. -/
def requiresAddressedValidation : ValidationConditionLeaf model → Bool
  | .orderedNumeric _ comparison =>
      comparison.requiresAddressedValidation
  | .groupPresence _ reference =>
      !(model.repeatableScopeForGroupPath reference.path).isEmpty
  | .repeatableFieldPresence _ _ => true
  | _ => false

/-- Static admission reuses each leaf family's existing checked core predicate. -/
def wellFormedBool (rowGroup : GroupPath) :
    ValidationConditionLeaf model → Bool
  | .flat condition => condition.wellFormedBool model
  | .numeric scope comparison =>
      comparison.wellFormedInBool model rowGroup scope
  | .orderedNumeric scope comparison =>
      comparison.wellFormedInBool rowGroup scope
  | .groupPresence _ reference =>
      reference.presenceWellFormedBool model rowGroup
  | .groupList _ operands =>
      ResolvedGroupListOperands.wellFormedBool operands model rowGroup
  | .repeatableFieldPresence _ declaration =>
      match model.lookupUniqueId declaration.id with
      | .ok checked =>
          checked == declaration && !declaration.repeatableScope.isEmpty
      | .error _ => false

/-- Evaluate one reached leaf with its own relevance rule. Ordinary numeric expressions require every field atom, ordered numeric atoms gate their own reached sources, and flat leaf rules retain their existing operator-specific checks. -/
def evalSelected (context : ValidationEvaluationContext)
    (isRelevant : FlatRelevance) :
    ValidationConditionLeaf model → Verdict
  | .flat condition => condition.evalSelected context.fields isRelevant
  | .numeric _ comparison =>
      if comparison.allRelevant isRelevant then
        comparison.evalSelectedWithGroups context
      else .unknown
  | .orderedNumeric _ comparison =>
      comparison.evalSelected context isRelevant
  | .groupPresence operator reference =>
      match context.groups reference.path with
      | some state => operator.eval state
      | none => .unknown
  | .groupList operator operands =>
      (operator.evalPresence
        (operands.map fun operand => operand.evalPresence context isRelevant)).asConservativeVerdict
  | .repeatableFieldPresence _ _ => .unknown

/-- Evaluate one addressed leaf through the same relevance rules. Only the model-indexed ordered numeric branch can produce a structural addressing error; every existing scalar/group leaf remains the exact pure evaluator lifted into that channel. -/
def evalAddressed (context : AddressedValidationEvaluationContext model) :
    ValidationConditionLeaf model → Except CheckedAddressingError Verdict
  | .orderedNumeric _ comparison => comparison.evalAddressed context
  | .groupPresence operator reference =>
      match context.input with
      | .legacy _ _ =>
          let leaf : ValidationConditionLeaf model :=
            .groupPresence operator reference
          pure (leaf.evalSelected context.scalar context.directRelevant)
      | .checked document => do
          let input ←
            (document.groupPresenceInput reference.path context.outer
              .fullyRelevant false).mapError .group
          pure (operator.eval input.derive)
  | .repeatableFieldPresence operator declaration => do
      pure (operator.eval
        (observeCell .validation
          (← context.readCell context.outer declaration.id)))
  | leaf => pure (leaf.evalSelected context.scalar context.directRelevant)

end ValidationConditionLeaf

namespace ValidationCondition

def canFireOnEmpty (condition : ValidationCondition model) : Bool :=
  condition.evalBool ValidationConditionLeaf.canFireOnEmpty

def referencesField (condition : ValidationCondition model)
    (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesField field

private def repeatableScopePrefix : List RepeatableLevel →
    List RepeatableLevel → Bool
  | [], _ => true
  | _, [] => false
  | left :: leftRest, right :: rightRest =>
      left == right && repeatableScopePrefix leftRest rightRest

inductive RuleIterationScopeError where
  | incompatibleScopes (left right : List RepeatableLevel)
  deriving Repr, DecidableEq

private def mergeIterationScopes
    (left right : Option (List RepeatableLevel)) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  match left, right with
  | none, scope | scope, none => pure scope
  | some leftScope, some rightScope =>
      if repeatableScopePrefix leftScope rightScope then
        pure (some rightScope)
      else if repeatableScopePrefix rightScope leftScope then
        pure (some leftScope)
      else
        throw (.incompatibleScopes leftScope rightScope)

private def checkedStarBindingScope
    (source : CheckedStarFieldPath model) :
    Option (List RepeatableLevel) :=
  let scope := source.bindingScope
  if scope.isEmpty then none else some scope

private def mergeIterationScopeList :
    List (Option (List RepeatableLevel)) →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | [] => pure none
  | scope :: remaining => do
      mergeIterationScopes scope (← mergeIterationScopeList remaining)

private def repeatableScopeThrough :
    List RepeatableLevel → RepeatableLevel →
      Option (List RepeatableLevel)
  | [], _ => none
  | level :: remaining, target =>
      if level == target then
        some [level]
      else
        (repeatableScopeThrough remaining target).map (level :: ·)

private def outerHavingNumberIterationScope
    (model : FlatModel) (reference : HavingNumberRef) :
    Option (List RepeatableLevel) :=
  match reference.origin with
  | .inner => none
  | .outer =>
      match model.lookupUniqueId reference.field.id with
      | .error _ => none
      | .ok declaration =>
          if declaration.repeatableScope.isEmpty then
            none
          else
            some declaration.repeatableScope

private def outerHavingRepetitionIterationScope
    (outerLevels : List RepeatableLevel)
    (reference : HavingRepetitionRef) :
    Option (List RepeatableLevel) :=
  match reference.origin with
  | .inner => none
  | .outer => repeatableScopeThrough outerLevels reference.level

private def correlatedHavingOuterIterationScopes
    (model : FlatModel) (outerLevels : List RepeatableLevel) :
    CorrelatedHaving → List (Option (List RepeatableLevel))
  | .leaf (.compareNumbers _ left right) =>
      [outerHavingNumberIterationScope model left,
        outerHavingNumberIterationScope model right]
  | .leaf (.compareRepetitions _ left right) =>
      [outerHavingRepetitionIterationScope outerLevels left,
        outerHavingRepetitionIterationScope outerLevels right]
  | .and left right | .or left right =>
      correlatedHavingOuterIterationScopes model outerLevels left ++
        correlatedHavingOuterIterationScopes model outerLevels right

private def checkedHavingOuterIterationScope
    (checked : CheckedStarHaving model source declaringGroup) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  mergeIterationScopeList
    (correlatedHavingOuterIterationScopes model
      (model.repeatableScopeForGroupPath declaringGroup)
      checked.condition)

private def checkedNumberOperandIterationScope :
    CheckedNumberEntityOperand model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .field _ => pure none
  | .star source => pure (checkedStarBindingScope source.source)
  | .starHaving source => do
      mergeIterationScopes
        (checkedStarBindingScope source.source.source)
        (← checkedHavingOuterIterationScope source.filter)

private def checkedTokenOperandIterationScope :
    CheckedTokenEntityOperand model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .field _ => pure none
  | .star source =>
      match source.filter with
      | none => pure (checkedStarBindingScope source.source)
      | some filter => do
          mergeIterationScopes
            (checkedStarBindingScope source.source)
            (← checkedHavingOuterIterationScope filter)

private def checkedNumberSourceIterationScope
    (source : CheckedNumberEntitySource model) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) := do
  mergeIterationScopeList
    (← source.operands.mapM checkedNumberOperandIterationScope)

private def checkedTokenSourceIterationScope
    (source : CheckedTokenEntitySource model) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) := do
  mergeIterationScopeList
    (← source.operands.mapM checkedTokenOperandIterationScope)

private def ordinaryNumericAtomFieldDeclaration?
    (model : FlatModel) :
    NumericValidationAtom → Option FlatFieldDecl
  | .field source =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toNumberField? == some source then
            some declaration
          else none
      | .error _ => none
  | .stringLength source =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toStringValueField? == some source then
            some declaration
          else none
      | .error _ => none
  | .fieldValueAsNumber source =>
      model.certifiedFieldValueAsNumberDeclaration? source
  | _ => none

private def ordinaryNumericAtomRepeatableDeclaration?
    (model : FlatModel) (source : NumericValidationAtom) :
    Option FlatFieldDecl := do
  let declaration ← ordinaryNumericAtomFieldDeclaration? model source
  if declaration.repeatableScope.isEmpty then none else some declaration

private def ordinaryNumericAtomIterationScope
    (model : FlatModel) (source : NumericValidationAtom) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  pure ((ordinaryNumericAtomRepeatableDeclaration? model source).map
    (·.repeatableScope))

private def orderedNumericAtomIterationScope :
    OrderedNumericValidationAtom model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .ordinary source => ordinaryNumericAtomIterationScope model source
  | .firstFilled source | .valueCount _ source | .aggregate _ source =>
      checkedNumberSourceIterationScope source
  | .tokenValueCount source =>
      checkedTokenSourceIterationScope source.source
  | .sumOfProducts source =>
      mergeIterationScopes
        (checkedStarBindingScope source.left.source)
        (checkedStarBindingScope source.right.source)

private def authoredNumericIterationScope
    (scopeOf : Atom →
      Except RuleIterationScopeError (Option (List RepeatableLevel))) :
    AuthoredNumericExpr Atom →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .atom atom => scopeOf atom
  | .literal _ => pure none
  | .group body | .abs body | .extremumCall _ body | .round _ _ body =>
      authoredNumericIterationScope scopeOf body
  | .binary _ left right | .power left right | .extremum _ left right => do
      mergeIterationScopes
        (← authoredNumericIterationScope scopeOf left)
        (← authoredNumericIterationScope scopeOf right)

private def orderedNumericComparisonIterationScope
    (comparison : OrderedNumericComparison model) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) := do
  mergeIterationScopes
    (← authoredNumericIterationScope
      orderedNumericAtomIterationScope comparison.left)
    (← authoredNumericIterationScope
      orderedNumericAtomIterationScope comparison.right)

/-- Derive one ordinary nonparallel rule-iteration scope from repeatable references. Ordinary references contribute their complete declaration scope; a star contributes only its nonempty binding prefix strictly above the first star. Nested compatible references select the deeper scope; sibling/cross-branch scopes remain explicit unsupported parallel work. -/
def ordinaryIterationScope :
    ValidationCondition model →
      Except RuleIterationScopeError (Option (List RepeatableLevel))
  | .leaf (.repeatableFieldPresence _ declaration) =>
      pure (some declaration.repeatableScope)
  | .leaf (.groupPresence _ reference) =>
      let scope := model.repeatableScopeForGroupPath reference.path
      pure (if scope.isEmpty then none else some scope)
  | .leaf (.orderedNumeric _ comparison) =>
      orderedNumericComparisonIterationScope comparison
  | .leaf _ => pure none
  | .and left right | .or left right => do
      mergeIterationScopes
        (← ordinaryIterationScope left) (← ordinaryIterationScope right)

/-- Checked static legality for one condition across every derived ordinary repeatable level. `insufficient` preserves an operator family whose level-local guard rule is not yet classified instead of guessing legal or illegal. -/
inductive IterationLegality where
  | legal
  | invalid (level : RepeatableLevel)
  | insufficient (level : RepeatableLevel)
  deriving Repr, DecidableEq

/-- The kernel's direct Number/literal visitor treats exactly these ordinary operators as empty-zero negative conditions. Tolerance and the other ordinary directions remain admitted for this source shape. -/
private def directEmptyZeroIsUnguarded :
    NumericValidationOp → Bool
  | .ordinary .equal | .ordinary .lessEqual
  | .ordinary .greaterEqual => true
  | _ => false

private def directOrdinaryZeroSensitiveScope?
    (model : FlatModel) :
    AuthoredNumericExpr (OrderedNumericValidationAtom model) →
      Option (List RepeatableLevel)
  | .atom (.ordinary source) =>
      (ordinaryNumericAtomFieldDeclaration? model source).map
        (·.repeatableScope)
  | _ => none

end ValidationCondition

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
      (ordinaryNumericAtomRepeatableDeclaration? model source).toList
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
  | .leaf _ => []
  | .and left right | .or left right =>
      ordinaryRepeatableFields left ++ ordinaryRepeatableFields right

/-- The first whole-rule route accepts established nonrepeatable flat leaves, ordinary repeatable field/group presence, and the checked same-group addressed Number policy. Specialized star sources retain their existing owners until their rule-environment bridge closes. -/
def supportsOrdinaryIteration
    (condition : ValidationCondition model) : Bool :=
  condition.allLeaves fun
    | .flat _ | .groupPresence _ _ | .repeatableFieldPresence _ _ => true
    | .orderedNumeric .sameGroupAddressed _ => true
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

/-- Apply the ordinary full-validation content gate to the addressed tree without sampling any repeatable source on an ineligible empty row. -/
def evalAddressedFull (condition : ValidationCondition model)
    (context : AddressedValidationEvaluationContext model)
    (hasContent : Bool) : Except CheckedAddressingError Verdict :=
  if hasContent || condition.canFireOnEmpty then condition.evalAddressed context
  else pure .notFired

end ValidationCondition

inductive ValidationConditionAssemblyError where
  | invalidModel (error : ResolveError)
  | groupReference (error : SingleGroupElabError)
  | fieldReference (error : ResolveError)
  | repeatableFieldRequired (path : List String)
  | unknownGroup (path : GroupPath)
  | repeatableGroupRequiresAddress (path : GroupPath)
  | emptyGroupList
  | groupListNeedsMultipleOperands
  | rootGroupInGroupList (path : GroupPath)
  | rootGroupRequiresSoleOperand (path : GroupPath)
  | overlappingGroupListOperands (left right : List String)
  | rowGroupMismatch (left right : GroupPath)
  | incoherentCore
  deriving Repr, DecidableEq

/-- A mixed resolved tree certified against one validated model and one exact rule-instance group. -/
structure CheckedValidationCondition (model : FlatModel) where
  rowGroup : GroupPath
  core : ValidationCondition model
  modelWellFormed : model.validate.isOk = true
  wellFormed : core.wellFormedBool rowGroup = true

private def ValidationConditionAssemblyError.ofFixedGroupReferenceError :
    FixedGroupReferenceError → ValidationConditionAssemblyError
  | .reference error => .groupReference error
  | .unknownGroup path => .unknownGroup path
  | .repeatableGroupRequiresAddress path =>
      .repeatableGroupRequiresAddress path

namespace CheckedValidationCondition

/-- Public checked-tree query used by Kernel 30.8.1 partial-validation consumers before relevance or execution. -/
def hasHaving (condition : CheckedValidationCondition model) : Bool :=
  condition.core.hasHaving

/-- Certify a resolved mixed core once after a semantic desugaring has assembled its complete tree. -/
def checkCore (model : FlatModel) (rowGroup : GroupPath)
    (core : ValidationCondition model) (modelWellFormed : model.validate.isOk = true) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  if hCore : core.wellFormedBool rowGroup = true then
    .ok { rowGroup, core, modelWellFormed, wellFormed := hCore }
  else
    .error .incoherentCore

/-- Lift a checked flat tree without nesting or changing its connective shape. -/
def fromFlat (condition : CheckedFlatCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model condition.rowGroup (ValidationCondition.flat condition.core)
    condition.modelWellFormed

/-- Lift one checked numeric comparison at its certified rule-instance group. -/
def fromNumeric (comparison : CheckedNumericComparison model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model comparison.rowGroup
    (ValidationCondition.numericIn comparison.operandScope comparison.core)
    comparison.modelWellFormed

/-- Lift one checked ordered-numeric comparison without reconstructing or flattening its authored expression tree. -/
def fromOrderedNumeric
    (comparison : CheckedOrderedNumericComparison model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  checkCore model comparison.rowGroup
    (ValidationCondition.orderedNumericIn
      comparison.operandScope comparison.core)
    comparison.modelWellFormed

  /-- Resolve and certify one group-presence predicate against the same model and declaring group used by the surrounding rule. Repeatable ancestry is retained for the addressed whole-rule route rather than rejected as a fixed-list operand. -/
def fromGroupPresence (model : FlatModel) (rowGroup : GroupPath)
    (reference : SurfaceGroupReference) (operator : GroupPresenceOperator) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let resolved ← reference.resolveAgainst rowGroup
        |>.mapError ValidationConditionAssemblyError.groupReference
      if !model.hasGroupPath resolved.path then
        throw (.unknownGroup resolved.path)
      checkCore model rowGroup
        (ValidationCondition.groupPresence operator resolved)
        (by rw [hModel]; rfl)

/-- Resolve one ordinary non-starred repeatable field presence reference. The declaration itself is the checked source; no wildcard topology or caller-supplied environment is manufactured here. -/
def fromRepeatableFieldPresence (model : FlatModel) (rowGroup : GroupPath)
    (operator : RepeatableFieldPresenceOperator)
    (reference : SurfaceFieldPath) :
    Except ValidationConditionAssemblyError
      (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let declaration ←
        (model.resolveFieldDeclarationUnchecked rowGroup reference)
          |>.mapError .fieldReference
      if declaration.repeatableScope.isEmpty then
        throw (.repeatableFieldRequired declaration.path)
      checkCore model rowGroup
        (ValidationCondition.repeatableFieldPresence operator declaration)
        (by rw [hModel]; rfl)

private def resolveGroupListOperand (model : FlatModel) (rowGroup : GroupPath) :
    SurfaceGroupListOperand →
      Except ValidationConditionAssemblyError ResolvedGroupListOperand
  | .field reference => do
      let declaration ←
        (model.resolveNonrepeatableFieldUnchecked rowGroup reference).mapError .fieldReference
      pure (.field declaration)
  | .group reference => do
      let resolved ← model.resolveFixedGroupReference rowGroup reference
        |>.mapError ValidationConditionAssemblyError.ofFixedGroupReferenceError
      pure (.group resolved)

private def resolveGroupListOperands (model : FlatModel) (rowGroup : GroupPath) :
    List SurfaceGroupListOperand →
      Except ValidationConditionAssemblyError (List ResolvedGroupListOperand)
  | [] => pure []
  | operand :: rest => do
      let resolved ← resolveGroupListOperand model rowGroup operand
      pure (resolved :: (← resolveGroupListOperands model rowGroup rest))

/-- Fixed singletons have an existing checked scalar owner. Keeping them out of the list leaf prevents a second representation of field or group presence. -/
private def singletonGroupListCondition? (operator : GroupFillQuantifier) :
    ResolvedGroupListOperand → Option (ValidationCondition model)
  | .field declaration =>
      match operator with
      | .atLeastOneGroupFilled =>
          some (ValidationCondition.flat
            (.fieldFilled declaration.toPresenceField))
      | .noGroupFilled =>
          some (ValidationCondition.flat
            (.fieldNotFilled declaration.toPresenceField))
      | .allGroupsFilled | .notAllGroupsFilled
      | .groupsNotCollectivelyFilled => none
  | .group reference =>
      match operator with
      | .atLeastOneGroupFilled =>
          some (ValidationCondition.groupPresence .filled reference)
      | .noGroupFilled =>
          some (ValidationCondition.groupPresence .notFilled reference)
      | .allGroupsFilled | .notAllGroupsFilled
      | .groupsNotCollectivelyFilled => none

/-- Resolve one fixed nonrepeatable field/group list and enforce the kernel's shared duplicate/overlap checks plus its operator-specific arity and root-group gates. Starred group operands remain with the checked SG2 topology owner. -/
def fromGroupList (model : FlatModel) (rowGroup : GroupPath)
    (operator : GroupFillQuantifier)
    (operands : List SurfaceGroupListOperand) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  match hModel : model.validate with
  | .error error => .error (.invalidModel error)
  | .ok () => do
      let resolved ← resolveGroupListOperands model rowGroup operands
      if resolved.isEmpty then throw .emptyGroupList
      match ResolvedGroupListOperands.firstOverlap? resolved with
      | some (left, right) =>
          throw (ValidationConditionAssemblyError.overlappingGroupListOperands left right)
      | none => pure ()
      match resolved.find? ResolvedGroupListOperand.isRootGroup with
      | some root =>
          if operator.requiresMultipleOperands then
            throw (.rootGroupInGroupList root.entityPath)
          else if resolved.length != 1 then
            throw (.rootGroupRequiresSoleOperand root.entityPath)
      | none => pure ()
      match resolved with
      | [operand] =>
          match singletonGroupListCondition? operator operand with
          | some condition =>
              checkCore model rowGroup condition (by rw [hModel]; rfl)
          | none => throw .groupListNeedsMultipleOperands
      | _ =>
          checkCore model rowGroup (ValidationCondition.groupList operator resolved)
            (by rw [hModel]; rfl)

private def combine (constructor : ValidationCondition model →
    ValidationCondition model → ValidationCondition model)
    (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  if left.rowGroup == right.rowGroup then
    checkCore model left.rowGroup (constructor left.core right.core)
      left.modelWellFormed
  else
    .error (.rowGroupMismatch left.rowGroup right.rowGroup)

def and (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  combine .and left right

def or (left right : CheckedValidationCondition model) :
    Except ValidationConditionAssemblyError (CheckedValidationCondition model) :=
  combine .or left right

end CheckedValidationCondition

end A12Kernel
