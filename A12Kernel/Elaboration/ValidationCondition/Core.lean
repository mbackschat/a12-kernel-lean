import A12Kernel.Elaboration.NumericValidation
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.RepetitionNotUnique
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Elaboration.ValidationContext

/-! # Shared resolved validation conditions

This boundary joins the established flat leaves and resolved numeric-expression comparisons under one connective tree. It deliberately begins after each leaf family's checked elaboration; a later checked whole-rule capsule must preserve those certificates rather than accepting forged cores.
-/

/-! This focused module owns resolved validation-condition leaves, connective evaluation, dependency discovery, and iteration-scope derivation. -/

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
  | repetitionNotUnique
      (source : CheckedRepetitionNotUniqueSource model)

/-- One checked connective tree whose leaves retain their family-specific resolved certificates and evaluation policies. -/
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

/-- Embed one checked branch-independent RNU source as an ordinary condition leaf. Whole-rule execution owns the once-per-scope result preparation. -/
def repetitionNotUnique
    (source : CheckedRepetitionNotUniqueSource model) :
    ValidationCondition model :=
  .leaf (.repetitionNotUnique source)

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
  | .repetitionNotUnique _ => false

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
  | .repetitionNotUnique source, field =>
      source.keys.any fun key => key.fieldId == field

/-- Whether a leaf retains any `Having` filter in its checked source. Only the model-indexed ordered numeric carrier can currently own such a source; scalar leaves cannot manufacture the marker. -/
def hasHaving : ValidationConditionLeaf model → Bool
  | .orderedNumeric _ comparison => comparison.hasHaving
  | .flat _ | .numeric _ _ | .groupPresence _ _ | .groupList _ _
  | .repeatableFieldPresence _ _ | .repetitionNotUnique _ => false

/-- Whether this leaf retains a repeatable numeric source and therefore cannot use the scalar checked evaluator. -/
def requiresAddressedValidation : ValidationConditionLeaf model → Bool
  | .orderedNumeric _ comparison =>
      comparison.requiresAddressedValidation
  | .groupPresence _ reference =>
      !(model.repeatableScopeForGroupPath reference.path).isEmpty
  | .repeatableFieldPresence _ _ => true
  | .repetitionNotUnique _ => true
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
  | .repetitionNotUnique source =>
      source.wellFormedBool rowGroup

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
  | .repetitionNotUnique _ => .unknown

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
  | .repetitionNotUnique _ =>
      .error (.repetitionNotUniqueResult context.outer)
  | leaf => pure (leaf.evalSelected context.scalar context.directRelevant)

/-- Evaluate one reached leaf with the rule-owned current-row RNU result. Every other leaf delegates to the established addressed evaluator unchanged. -/
def evalAddressedWithRepetitionNotUnique
    (context : AddressedValidationEvaluationContext model)
    (result? : Option RepetitionNotUniqueResult) :
    ValidationConditionLeaf model → Except CheckedAddressingError Verdict
  | .repetitionNotUnique _ =>
      match result? with
      | some result =>
          if result.row == context.outer then
            pure result.verdict
          else
            .error (.repetitionNotUniqueResult context.outer)
      | none => .error (.repetitionNotUniqueResult context.outer)
  | leaf => leaf.evalAddressed context

end ValidationConditionLeaf

namespace ValidationCondition

def canFireOnEmpty (condition : ValidationCondition model) : Bool :=
  condition.evalBool ValidationConditionLeaf.canFireOnEmpty

def referencesField (condition : ValidationCondition model)
    (field : FieldId) : Bool :=
  condition.anyLeaf fun leaf => leaf.referencesField field

/-- The checked condition retains at most one RNU source; exposing it lets the ordinary rule prepare the branch-independent relation before the connective walk. -/
def repetitionNotUniqueSources
    (condition : ValidationCondition model) :
    List (CheckedRepetitionNotUniqueSource model) :=
  match condition with
  | .leaf (.repetitionNotUnique source) => [source]
  | .leaf _ => []
  | .and left right | .or left right =>
      repetitionNotUniqueSources left ++ repetitionNotUniqueSources right

def repetitionNotUniqueSource?
    (condition : ValidationCondition model) :
    Option (CheckedRepetitionNotUniqueSource model) :=
  condition.repetitionNotUniqueSources.head?

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

def checkedStarBindingScope
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

private def temporalDifferenceOperandDeclarations?
    (model : FlatModel) (accepts : FlatTemporalField → Bool) :
    ResolvedDateDifferenceOperand → Option (List FlatFieldDecl)
  | .field source =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toTemporalField? == some source && accepts source then
            some [declaration]
          else none
      | .error _ => none
  | .baseYear year _ =>
      if model.baseYear == some year then some [] else none

def ordinaryNumericAtomFieldDeclarations?
    (model : FlatModel) :
    NumericValidationAtom → Option (List FlatFieldDecl)
  | .field source =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toNumberField? == some source then
            some [declaration]
          else none
      | .error _ => none
  | .temporalFieldPart source part =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toTemporalField? == some source &&
              part.admittedBy source model.hasBaseYear then
            some [declaration]
          else none
      | .error _ => none
  | .stringLength source =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toStringValueField? == some source then
            some [declaration]
          else none
      | .error _ => none
  | .stringRange source _ _ =>
      match model.lookupUniqueId source.id with
      | .ok declaration =>
          if declaration.toStringValueField? == some source then
            some [declaration]
          else none
      | .error _ => none
  | .fieldValueAsNumber source =>
      (model.certifiedFieldValueAsNumberDeclaration? source).map (· :: [])
  | .dateDifference unit left right => do
      let declarations := temporalDifferenceOperandDeclarations? model
        (fun source => source.kind == .date &&
          unit.admittedBy model.hasBaseYear source.components)
      let leftDeclarations ← declarations left
      let rightDeclarations ← declarations right
      if unit.compatible model.hasBaseYear left.components right.components then
        some (leftDeclarations ++ rightDeclarations)
      else none
  | .dateTimeDifference unit left right => do
      let declarationFor (source : FlatTemporalField) := do
        let declaration ← model.lookupUniqueId source.id |>.toOption
        if declaration.toTemporalField? == some source &&
            source.kind == .dateTime &&
            unit.admittedBy source.components then
          some declaration
        else
          none
      let leftDeclaration ← declarationFor left
      let rightDeclaration ← declarationFor right
      if unit.compatible left.components right.components then
        some [leftDeclaration, rightDeclaration]
      else
        none
  | .dayDifference profile left right => do
      if ModelZone.ConcreteProfile.ofId? model.timeZoneId != some profile then
        none
      let declarations := temporalDifferenceOperandDeclarations? model
        (fun source =>
          CalendarDayDifference.admittedBy source.kind source.components)
      let leftDeclarations ← declarations left
      let rightDeclarations ← declarations right
      if CalendarDayDifference.yearCompatible model.hasBaseYear
          left.components right.components then
        some (leftDeclarations ++ rightDeclarations)
      else none
  | _ => none

private def ordinaryNumericAtomIterationScope
    (model : FlatModel) (source : NumericValidationAtom) :
    Except RuleIterationScopeError (Option (List RepeatableLevel)) :=
  match ordinaryNumericAtomFieldDeclarations? model source with
  | none => pure none
  | some declarations =>
      mergeIterationScopeList (declarations.map fun declaration =>
        if declaration.repeatableScope.isEmpty then
          none
        else
          some declaration.repeatableScope)

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

def orderedNumericComparisonIterationScope
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
  | .leaf (.repetitionNotUnique source) =>
      pure (some (source.topology.path.axes.map (·.level)))
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
def directEmptyZeroIsUnguarded :
    NumericValidationOp → Bool
  | .ordinary .equal | .ordinary .lessEqual
  | .ordinary .greaterEqual => true
  | _ => false

def directOrdinaryZeroSensitiveScope?
    (model : FlatModel) :
    AuthoredNumericExpr (OrderedNumericValidationAtom model) →
      Option (List RepeatableLevel)
  | .atom (.ordinary source) =>
      match ordinaryNumericAtomFieldDeclarations? model source with
      | none => none
      | some declarations =>
          match mergeIterationScopeList (declarations.map fun declaration =>
              if declaration.repeatableScope.isEmpty then
                none
              else
                some declaration.repeatableScope) with
          | .ok scope => scope
          | .error _ => none
  | _ => none

end ValidationCondition

end A12Kernel
