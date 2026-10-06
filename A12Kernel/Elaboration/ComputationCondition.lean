import A12Kernel.Elaboration.KeyedGroupPresence
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.ComputationGroupDependency
import A12Kernel.Elaboration.FieldFillList
import A12Kernel.Elaboration.Flat.ComputationBinding
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Elaboration.NumericValidation.Core
import A12Kernel.Elaboration.Flat.FieldValueRead
import A12Kernel.Elaboration.Flat.Condition.Surface

/-! # Model-certified computation conditions

Presence guards accept every scalar declaration the target's row binds, a nonrepeatable one for a fixed target. Numeric guards retain Number declarations and structural coordinates through the shared numeric comparison admission. Text guards reuse validation's checked String/Enumeration projections and comparison gate at the target's scope. Value-kind restrictions remain absent from presence. Group guards retain exact subtree membership, the addressed content slice and the target-bound group identity; their target ban differs from operand membership.
-/

namespace A12Kernel

/-- Numeric guard admission retains declaration metadata and the target's binding scope. -/
def ComputationNumericAtom.admitted (model : FlatModel) (scope : List RepeatableLevel) :
    ComputationNumericAtom → Bool
  | .field source => match model.lookupUniqueId source.id with
      | .ok declaration => declaration.toNumberField? == some source &&
          declaration.repeatableScope.isPrefixOf scope
      | .error _ => false
  | .repetition source => model.hasGroupPath source.path &&
      source.scope == model.repeatableScopeForGroupPath source.path &&
      source.scope.isPrefixOf scope &&
      source.level == (model.repeatableGroups.find? (·.path == source.path)).map (·.level)
  | .baseYear year => model.baseYear == some year

def computationNumericGuardAdmitted (comparison : NumericComparisonOf ComputationNumericAtom)
    (model : FlatModel) (scope : List RepeatableLevel) : Bool :=
  comparison.admittedWith (ComputationNumericAtom.admitted model scope)
    ComputationNumericAtom.summary

/-- A resolved fill source must retain the model's exact repeatable axes and bind its outer prefix. -/
def ComputationFillSource.admitted (model : FlatModel) (scope : List RepeatableLevel) :
    ComputationFillSource → Bool
  | .direct field => match model.lookupUniqueId field with
      | .ok declaration => declaration.repeatableScope.isPrefixOf scope
      | .error _ => false
  | .expanded field axes boundCount => match model.lookupUniqueId field with
      | .ok declaration => model.repeatableAxesForScope? declaration.repeatableScope == some axes &&
          boundCount ≤ axes.length && ((axes.take boundCount).map (·.level)).isPrefixOf scope
      | .error _ => false

/-- Retain exact model-derived membership and content while binding the operand to the target row. -/
def ComputationGroupOperand.admitted (source : ComputationGroupOperand)
    (model : FlatModel) (scope : List RepeatableLevel) : Bool :=
  model.hasGroupPath source.reference.path &&
    source.content == model.computationGroupSource source.reference.path &&
    source.members == (model.groupSubtreeFields source.reference.path).map (·.id) &&
    source.reference.boundRepeatableScope == source.content.scope &&
    match source.starPath with
    | none => source.content.scope.isPrefixOf scope
    | some path =>
        model.repeatableAxesForScope? source.content.scope == some path.axes &&
          path.firstStar < path.axes.length && path.bindingScope.isPrefixOf scope

/-- Scalar equality preserves exact model-owned kind and target-bound field identity. -/
def FlatModel.admitsScalarGuardIn (model : FlatModel) (scope : List RepeatableLevel)
    (comparison : FlatComparison) : Bool :=
  let supported := match comparison with
    | .boolean .. | .confirm .. => true
    | _ => false
  supported && comparison.fields.all fun field =>
    model.ownsField field && (model.fieldRepeatableScope field.id).isPrefixOf scope

namespace ComputationCondition

/-- Check model ownership and fixed-target admission for every guard leaf. -/
def wellFormedBool (condition : ComputationCondition) (model : FlatModel) : Bool :=
  match condition with
  | .leaf (.predicate source) => nomatch source
  | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
      match model.lookupUniqueId field with
      | .ok declaration => declaration.repeatableScope.isEmpty
      | .error _ => false
  | .leaf (.fieldFill _ sources) => !sources.isEmpty && sources.all (·.admitted model [])
  | .leaf (.groupPresence _ source) => source.admitted model []
  | .leaf (.text comparison) => model.admitsTextComparisonIn [] comparison
  | .leaf (.scalar comparison) => model.admitsScalarGuardIn [] comparison
  | .leaf (.numeric comparison) => computationNumericGuardAdmitted comparison model []
  | .and left right | .or left right =>
      left.wellFormedBool model && right.wellFormedBool model

/-- Check each leaf against the target row scope, retaining numeric authoring and metadata checks. -/
def rowBoundBool (condition : ComputationCondition) (model : FlatModel)
    (scope : List RepeatableLevel) : Bool :=
  match condition with
  | .leaf (.predicate source) => nomatch source
  | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
      match model.lookupUniqueId field with
      | .ok declaration => declaration.repeatableScope.isPrefixOf scope
      | .error _ => false
  | .leaf (.fieldFill _ sources) => !sources.isEmpty && sources.all (·.admitted model scope)
  | .leaf (.groupPresence _ source) => source.admitted model scope
  | .leaf (.text comparison) => model.admitsTextComparisonIn scope comparison
  | .leaf (.scalar comparison) => model.admitsScalarGuardIn scope comparison
  | .leaf (.numeric comparison) => computationNumericGuardAdmitted comparison model scope
  | .and left right | .or left right =>
      left.rowBoundBool model scope && right.rowBoundBool model scope

def WellFormed (condition : ComputationCondition) (model : FlatModel) : Prop :=
  condition.wellFormedBool model = true

end ComputationCondition

/-- A computation precondition retaining authored numeric expressions and field paths. -/
inductive SurfaceComputationConditionOf (Atom : Type) (Predicate : Type := Empty) where
  | fieldFilled (field : SurfaceFieldPath)
  | fieldNotFilled (field : SurfaceFieldPath)
  | text (op : SurfaceComparisonOp) (left : SurfaceTextFieldOperand)
      (right : Sum SurfaceTextFieldOperand String)
  | numeric (comparison : NumericComparisonOf Atom)
  | predicate (source : Predicate)
  | boolean (op : SurfaceComparisonOp) (field : SurfaceFieldPath) (expected : Bool)
  | fieldFill (operator : FieldFillQuantifier) (source : SurfaceFieldEntitySource)
  | groupPresence (operator : GroupPresenceOperator) (source : SurfaceGroupReference)
  | groupFill (operator : GroupFillQuantifier) (source : SurfaceFieldEntitySource)
  | and (left right : SurfaceComputationConditionOf Atom Predicate)
  | or (left right : SurfaceComputationConditionOf Atom Predicate)
  deriving Repr, DecidableEq

abbrev SurfaceComputationCondition := SurfaceComputationConditionOf SurfaceNumericAtom

/-- Group-list gates retain their own arity and star policy after shared entity resolution. -/
inductive ComputationGroupListElabError where
  | shape (error : FieldEntityShapeElabError)
  | tooFewOperands
  | rootRequiresSoleOperand (path : GroupPath)
  | rootNotAllowed (path : GroupPath)
  | starNotAllowed (operator : GroupFillQuantifier)
  | unsupportedOperand
  deriving Repr, DecidableEq

/-- Guard errors retain the owning predicate family's admission failure. -/
inductive ComputationConditionElabError where
  | resolve (error : ResolveError)
  | numeric (error : NumericValidationElabError)
  | text (error : ElabError)
  | fieldFill (error : FieldFillListElabError)
  | groupPresence (error : FixedGroupReferenceError)
  | groupFill (error : ComputationGroupListElabError)
  deriving DecidableEq

instance : Repr ComputationConditionElabError where
  reprPrec error precedence := match error with
    | .resolve error => reprPrec (NumericValidationElabError.resolve error) precedence
    | .numeric error => reprPrec error precedence
    | .text error => reprPrec error precedence
    | .fieldFill error => reprPrec error precedence
    | .groupPresence error => reprPrec error precedence
    | .groupFill error => reprPrec error precedence

private def numericGuardError : NumericValidationElabError → ComputationConditionElabError
  | .resolve error => .resolve error
  | error => .numeric error

private def textGuardError : ElabError → ComputationConditionElabError
  | .resolve error => .resolve error
  | error => .text error

private def FlatModel.resolveComputationTextOperand (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (surface : SurfaceTextFieldOperand) :
    Except ElabError (FlatFieldDecl × FlatTextFieldOperand × DirectComparableField) := do
  let declaration ← (do
    let declaration ← displaceGroupRead
      (model.resolveComputationOperandUnchecked declaringGroup targetGroup surface.reference)
      (model.computationGroupRead declaringGroup targetGroup surface.reference)
    if let some error := declaration.projectedReadRefusal? surface.projectionRef then throw error
    pure declaration).mapError ElabError.resolve
  let resolved := match surface.projectionRef with
    | .stored => declaration.toTextFieldComparison?
    | projection => declaration.toEnumerationTextFieldComparison? projection
  let some (operand, profile) := resolved
    | throw (.textFieldOperandKindMismatch declaration.path declaration.policy.kind.surfaceKind)
  pure (declaration, operand, profile)

private def FlatModel.elaborateComputationTextGuard (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (op : SurfaceComparisonOp)
    (left : SurfaceTextFieldOperand) (right : Sum SurfaceTextFieldOperand String) :
    Except ElabError ComputationCondition := do
  let (declaration, leftOperand, leftProfile) ←
    model.resolveComputationTextOperand declaringGroup targetGroup left
  let right : Sum (FlatFieldDecl × FlatTextFieldOperand × DirectComparableField) String ←
    match right with
    | .inl operand => Sum.inl <$> model.resolveComputationTextOperand declaringGroup targetGroup operand
    | .inr literal => pure (.inr literal)
  let some equality := op.toEquality? | throw (.unsupportedOperator op)
  let comparison ← match right with
    | .inl (rightDeclaration, rightOperand, rightProfile) =>
        match classifyDirectFieldComparison leftProfile rightProfile with
        | .accepted => pure (FlatComparison.textFields equality leftOperand rightOperand)
        | .rejected error => throw (.enumerationComparability declaration.path rightDeclaration.path error)
    | .inr expected => match leftOperand with
        | .string field => pure (.string equality field expected)
        | .enumeration operand =>
            let .compare comparison ← elaborateEnumerationCore declaration op operand.projectionRef expected
              | throw .incoherentCore
            pure comparison
  if model.admitsTextComparisonIn (model.repeatableScopeForGroupPath targetGroup) comparison then
    pure (.leaf (.text comparison))
  else throw .incoherentCore

/-- Resolve one presence leaf's field as a computation operand, bound by the target's scope rather
than the declaring group's, a name reaching a group taking the group slot's class: a fixed group draws
`MVK_NO_GROUPS_ALLOWED` and an unbound repeatable one its level's class, as an unbound field does
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-computation-precondition-names)). -/
private def FlatModel.resolveComputationPresence (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (reference : SurfaceFieldPath) :
    Except ResolveError FieldId :=
  (·.id) <$> model.resolvePresenceOperand declaringGroup targetGroup reference
    (model.resolveComputationOperandUnchecked declaringGroup targetGroup reference)

private def FlatModel.resolveComputationGuardAtom (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) :
    SurfaceNumericAtom → Except NumericValidationElabError ComputationNumericAtom
  | .field reference => do
      let declaration ← (model.resolveComputationFieldValueRead declaringGroup targetGroup reference).mapError .resolve
      let some source := declaration.toNumberField? | throw (.fieldNotNumber declaration.path)
      pure (.field source)
  | .baseYear => match model.baseYear with
      | some year => pure (.baseYear year)
      | none => throw .baseYearNotDeclared
  | .currentRepetition reference => do
      let source : ResolvedNumericAtom FlatNumberField ←
        (model.resolveNumericCurrentRepetition declaringGroup
          (model.repeatableScopeForGroupPath targetGroup) reference).mapError .currentRepetitionSource
      match source with
      | .fixedCurrentRepetition group => pure (.repetition { path := group.path, scope := [], level := none })
      | .boundCurrentRepetition source => pure (.repetition source)
      | _ => throw .unsupportedExpression
  | _ => throw .unsupportedExpression

private def FlatModel.elaborateComputationNumericGuard (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (surface : SurfaceNumericComparison) :
    Except NumericValidationElabError ComputationCondition := do
  let left ← surface.left.mapM (model.resolveComputationGuardAtom declaringGroup targetGroup)
  let right ← surface.right.mapM (model.resolveComputationGuardAtom declaringGroup targetGroup)
  let comparison : NumericComparisonOf ComputationNumericAtom :=
    { left, right, op := surface.op, suppressExactScaleWarning := surface.suppressExactScaleWarning }
  if computationNumericGuardAdmitted comparison model (model.repeatableScopeForGroupPath targetGroup) then
    pure (.leaf (.numeric comparison))
  else throw .unsupportedExpression

/-- Resolve computation group lists with the common target-bound entity walk and overlap checks.
The operator chooses whether a sole/root/starred operand is legal before each entity contributes
its own presence leaves; fields are never replaced by their containing groups. -/
def FlatModel.elaborateComputationGroupListWith (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (operator : GroupFillQuantifier)
    (authored : SurfaceFieldEntitySource)
    (selected : ResolvedFieldEntityOperand model → Except ComputationGroupListElabError
      (ComputationConditionOf Atom Predicate × ComputationConditionOf Atom Predicate)) :
    Except ComputationGroupListElabError (ComputationConditionOf Atom Predicate) := do
  let scope := model.repeatableScopeForGroupPath targetGroup
  let operands ← (resolveFieldEntityOperands model declaringGroup scope (some targetGroup)
    targetGroup (authored.first :: authored.rest)).mapError .shape
  if let some unbound := model.firstUnboundComputationLevel? declaringGroup targetGroup
      (operands.map ResolvedFieldEntityOperand.bindingScope) then
    throw (.shape (.unboundOperandLevel unbound))
  if let some duplicate := firstDuplicateResolvedEntityOperand? operands then
    throw (.shape (match duplicate with
      | .field (field, _) | .indexed (field, _) => .duplicateOperand field
      | .fixedGroup path | .keyedGroup path _ => .duplicateGroupOperand path))
  if let some (left, right) := firstResolvedOperandOverlap? operands then
    throw (.shape (.overlappingOperands left right))
  if let some path := operands.findSome? ResolvedFieldEntityOperand.rootGroupPath? then
    if operator.requiresMultipleOperands then throw (.rootNotAllowed path)
    if operands.length != 1 then throw (.rootRequiresSoleOperand path)
  let isStarred : ResolvedFieldEntityOperand model → Bool
    | .keyed source => source.isStarredGroup
    | .starredGroup _ | .starredGroupPresence _ => true
    | _ => false
  if operator.requiresMultipleOperands then
    if operands.any isStarred then throw (.starNotAllowed operator)
    if operands.length < 2 then throw .tooFewOperands
  let group (reference : ResolvedGroupReference) (starPath : Option StarPath := none) :
      ComputationConditionOf Atom Predicate × ComputationConditionOf Atom Predicate :=
    let source : ComputationGroupOperand := {
      reference := { reference with boundRepeatableScope := model.repeatableScopeForGroupPath reference.path }
      content := model.computationGroupSource reference.path
      members := (model.groupSubtreeFields reference.path).map (·.id)
      starPath
      dependencyKind := if reference.isRoot && starPath.isNone then .conditionalPresence else .ordinaryList }
    (ConditionTree.leaf (.groupPresence .filled source), ConditionTree.leaf (.groupPresence .notFilled source))
  let conditions ← operands.mapM fun operand => match operand with
    | .field declaration .stored => pure (.leaf (.fieldFilled declaration.id), .leaf (.fieldNotFilled declaration.id))
    | operand@(.indexed _) | operand@(.keyed _) => selected operand
    | .group reference => pure (group reference)
    | .starredGroup source => pure (group { path := source.group.path, origin := .path } (some source.path))
    | .starredGroupPresence source => pure (group { path := source.groupPath, origin := .path } (some source.path))
    | _ => throw .unsupportedOperand
  match conditions with
  | [] => throw .tooFewOperands
  | first :: rest => pure (ComputationCondition.ofGroupListWith operator first rest)

def FlatModel.elaborateComputationGroupList (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) (operator : GroupFillQuantifier)
    (authored : SurfaceFieldEntitySource) : Except ComputationGroupListElabError ComputationCondition :=
  model.elaborateComputationGroupListWith declaringGroup targetGroup operator authored
    (fun _ => .error .unsupportedOperand)

/-- Resolve a precondition's names left to right against a validated model, so its first unresolved
name is the one reported. -/
def FlatModel.elaborateComputationCondition (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) :
    SurfaceComputationCondition → Except ComputationConditionElabError ComputationCondition
  | .predicate impossible => nomatch impossible
  | .groupFill operator source =>
      (model.elaborateComputationGroupList declaringGroup targetGroup operator source).mapError .groupFill
  | .groupPresence operator surface => do
      let reference ← (model.resolveFixedTargetGroupReference declaringGroup targetGroup surface).mapError .groupPresence
      let source : ComputationGroupOperand := {
        reference := { reference with boundRepeatableScope := model.repeatableScopeForGroupPath reference.path }
        content := model.computationGroupSource reference.path
        members := (model.groupSubtreeFields reference.path).map (·.id) }
      if !(source.admitted model (model.repeatableScopeForGroupPath targetGroup)) then
        throw (.groupPresence (.repeatableGroupRequiresAddress reference.path))
      pure (.leaf (.groupPresence operator source))
  | .fieldFill operator source => do
      let checked ← (elaborateComputationFieldFillList model declaringGroup targetGroup source).mapError .fieldFill
      let sources ← checked.computationSources.mapError .fieldFill
      pure (.leaf (.fieldFill operator sources))
  | .fieldFilled reference =>
      (.leaf ∘ .fieldFilled) <$> (model.resolveComputationPresence declaringGroup targetGroup reference).mapError .resolve
  | .fieldNotFilled reference =>
      (.leaf ∘ .fieldNotFilled) <$> (model.resolveComputationPresence declaringGroup targetGroup reference).mapError .resolve
  | .text op left right =>
      (model.elaborateComputationTextGuard declaringGroup targetGroup op left right).mapError textGuardError
  | .boolean op reference expected => do
      let declaration ← (model.resolveComputationFieldValueRead declaringGroup targetGroup reference).mapError .resolve
      let some equality := op.toEquality? | throw (.text (.unsupportedOperator op))
      let comparison ← match declaration.policy.kind with
        | .boolean => pure (FlatComparison.boolean equality { id := declaration.id } expected)
        | .confirm =>
            if expected then pure (.confirm equality { id := declaration.id })
            else throw (.text (.illegalConfirmLiteral declaration.path))
        | kind => throw (.text (.literalKindMismatch declaration.path kind.surfaceKind .boolean))
      pure (.leaf (.scalar comparison))
  | .numeric comparison =>
      (model.elaborateComputationNumericGuard declaringGroup targetGroup comparison).mapError numericGuardError
  | .and left right => do
      let left ← model.elaborateComputationCondition declaringGroup targetGroup left
      pure (.and left (← model.elaborateComputationCondition declaringGroup targetGroup right))
  | .or left right => do
      let left ← model.elaborateComputationCondition declaringGroup targetGroup left
      pure (.or left (← model.elaborateComputationCondition declaringGroup targetGroup right))

/-- An alternative whose guard its carrier admits, carrying that admission as evidence. -/
abbrev AdmittedComputationAlternative {Guard : Type} (admits : Guard → Bool) (Operation : Type) :=
  { alternative : ComputationAlternative Operation Guard // alternative.precondition.all admits = true }

private def admitRemainingGuards {Operation : Type} (admits : Guard → Bool)
    (position : Nat) :
    List (ComputationAlternative Operation Guard) →
      Except Nat (List (AdmittedComputationAlternative admits Operation))
  | [] => .ok []
  | alternative :: rest =>
      if hAdmitted : alternative.precondition.all admits = true then do
        pure (⟨alternative, hAdmitted⟩ :: (← admitRemainingGuards admits (position + 1) rest))
      else .error position

/-- Admit every alternative's guard in authored order, or the one-based position of the first its
carrier refuses. A table's certifier asks this of every alternative before any alternative's own
class, as the Kernel asks a guard's name and its index gates ahead of an unguarded alternative
wherever either stands
([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)), and
consumes the admissions instead of asking again. -/
def ComputationAlternative.admitGuards {Operation : Type} (admits : Guard → Bool)
    (first : ComputationAlternative Operation Guard) (remaining : List (ComputationAlternative Operation Guard)) :
    Except Nat (AdmittedComputationAlternative admits Operation ×
      List (AdmittedComputationAlternative admits Operation)) :=
  if hAdmitted : first.precondition.all admits = true then do
    pure (⟨first, hAdmitted⟩, ← admitRemainingGuards admits 2 remaining)
  else .error 1

end A12Kernel
