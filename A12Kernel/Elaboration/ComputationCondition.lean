import A12Kernel.Elaboration.Flat.ComputationBinding
import A12Kernel.Semantics.ComputationCondition
import A12Kernel.Elaboration.NumericValidation.Core
import A12Kernel.Elaboration.Flat.FieldValueRead

/-! # Model-certified computation conditions

Presence guards accept every scalar declaration the target's row binds, a nonrepeatable one for a fixed target. Numeric guards retain Number declarations and structural coordinates through the shared numeric comparison admission. Value-kind restrictions remain absent from presence.
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

namespace ComputationCondition

/-- Check model ownership and fixed-target admission for every guard leaf. -/
def wellFormedBool (condition : ComputationCondition) (model : FlatModel) : Bool :=
  match condition with
  | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
      match model.lookupUniqueId field with
      | .ok declaration => declaration.repeatableScope.isEmpty
      | .error _ => false
  | .leaf (.numeric comparison) => computationNumericGuardAdmitted comparison model []
  | .and left right | .or left right =>
      left.wellFormedBool model && right.wellFormedBool model

/-- Check each leaf against the target row scope, retaining numeric authoring and metadata checks. -/
def rowBoundBool (condition : ComputationCondition) (model : FlatModel)
    (scope : List RepeatableLevel) : Bool :=
  match condition with
  | .leaf (.fieldFilled field) | .leaf (.fieldNotFilled field) =>
      match model.lookupUniqueId field with
      | .ok declaration => declaration.repeatableScope.isPrefixOf scope
      | .error _ => false
  | .leaf (.numeric comparison) => computationNumericGuardAdmitted comparison model scope
  | .and left right | .or left right =>
      left.rowBoundBool model scope && right.rowBoundBool model scope

def WellFormed (condition : ComputationCondition) (model : FlatModel) : Prop :=
  condition.wellFormedBool model = true

end ComputationCondition

/-- A computation precondition retaining authored numeric expressions and field paths. -/
inductive SurfaceComputationCondition where
  | fieldFilled (field : SurfaceFieldPath)
  | fieldNotFilled (field : SurfaceFieldPath)
  | numeric (comparison : SurfaceNumericComparison)
  | and (left right : SurfaceComputationCondition)
  | or (left right : SurfaceComputationCondition)
  deriving Repr, DecidableEq

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

/-- Resolve a precondition's names left to right against a validated model, so its first unresolved
name is the one reported. -/
def FlatModel.elaborateComputationCondition (model : FlatModel)
    (declaringGroup targetGroup : GroupPath) :
    SurfaceComputationCondition → Except NumericValidationElabError ComputationCondition
  | .fieldFilled reference =>
      (.leaf ∘ .fieldFilled) <$> (model.resolveComputationPresence declaringGroup targetGroup reference).mapError .resolve
  | .fieldNotFilled reference =>
      (.leaf ∘ .fieldNotFilled) <$> (model.resolveComputationPresence declaringGroup targetGroup reference).mapError .resolve
  | .numeric comparison => model.elaborateComputationNumericGuard declaringGroup targetGroup comparison
  | .and left right => do
      let left ← model.elaborateComputationCondition declaringGroup targetGroup left
      pure (.and left (← model.elaborateComputationCondition declaringGroup targetGroup right))
  | .or left right => do
      let left ← model.elaborateComputationCondition declaringGroup targetGroup left
      pure (.or left (← model.elaborateComputationCondition declaringGroup targetGroup right))

/-- An alternative whose guard its carrier admits, carrying that admission as evidence. -/
abbrev AdmittedComputationAlternative (admits : ComputationCondition → Bool) (Operation : Type) :=
  { alternative : ComputationAlternative Operation // alternative.precondition.all admits = true }

private def admitRemainingGuards {Operation : Type} (admits : ComputationCondition → Bool)
    (position : Nat) :
    List (ComputationAlternative Operation) →
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
def ComputationAlternative.admitGuards {Operation : Type} (admits : ComputationCondition → Bool)
    (first : ComputationAlternative Operation) (remaining : List (ComputationAlternative Operation)) :
    Except Nat (AdmittedComputationAlternative admits Operation ×
      List (AdmittedComputationAlternative admits Operation)) :=
  if hAdmitted : first.precondition.all admits = true then do
    pure (⟨first, hAdmitted⟩, ← admitRemainingGuards admits 2 remaining)
  else .error 1

end A12Kernel
