import A12Kernel.Elaboration.AddressedRepeatableTarget
import A12Kernel.Elaboration.CheckedGroupPresence
import A12Kernel.Elaboration.SingleGroup
import A12Kernel.Semantics.NumericTarget

/-! # Fixed-group count into a repeatable Number target

This carrier owns the measured row-local `NumberOfFilledGroups` shape whose target and fixed child
groups share the declaring rule's already-bound repeatable scope. It does not widen the scalar
Number computation carrier: target scale and constraints, deeper target scope, and unbound operand
scope stay explicit boundaries.
-/

namespace A12Kernel

inductive RepeatableNumberFixedGroupCountElabError where
  | target (cause : AddressedRepeatableTargetElabError)
  | targetNotNumber (path : List String)
  | targetScaleOutsideObservedBoundary (path : List String) (scale : Nat)
  | targetConstraintsOutsideObservedBoundary (path : List String)
  | targetScopeMismatch (path : List String)
      (declaringScope targetScope : List RepeatableLevel)
  | group (cause : FixedGroupReferenceError)
  | groupScopeMismatch (path : GroupPath)
      (declaringScope groupScope : List RepeatableLevel)
  | needsMultipleOperands
  | overlappingOperands (left right : GroupPath)
  | rootOperand (path : GroupPath)
  | targetSelfReference (field : FieldId)
  deriving Repr, DecidableEq

/-- A repeatable integral Number target and the disjoint fixed child groups counted at each exact
target row. The private constructor keeps the measured same-scope and unconstrained-target boundary
attached to the runtime operation. -/
structure CheckedRepeatableNumberFixedGroupCountComputation (model : FlatModel) where
  private mk ::
  checkedTarget : CheckedAddressedRepeatableTarget model
  groups : List ResolvedGroupReference

/-- Check repeatable target placement, the measured integral unconstrained target profile, and the
shared fixed-group gates. Fixed groups below the declaring repeatable row are admitted only through
the scope certificate produced by `resolveRuleBoundFixedGroupReferences`. -/
def checkRepeatableNumberFixedGroupCountComputation
    (model : FlatModel) (declaringGroup : GroupPath) (targetField : FieldId)
    (surfaces : List SurfaceGroupReference) :
    Except RepeatableNumberFixedGroupCountElabError
      (CheckedRepeatableNumberFixedGroupCountComputation model) := do
  let checkedTarget ←
    checkAddressedRepeatableTarget model declaringGroup targetField
      |>.mapError .target
  let target ← match checkedTarget.declaration.toNumberField? with
    | some target => pure target
    | none => throw (.targetNotNumber checkedTarget.declaration.path)
  if target.info.scale != 0 then
    throw (.targetScaleOutsideObservedBoundary
      checkedTarget.declaration.path target.info.scale)
  if checkedTarget.declaration.numericTargetConstraints !=
      NumericTargetConstraints.unconstrained then
    throw (.targetConstraintsOutsideObservedBoundary checkedTarget.declaration.path)
  let declaringScope := model.repeatableScopeForGroupPath declaringGroup
  if checkedTarget.declaration.repeatableScope != declaringScope then
    throw (.targetScopeMismatch checkedTarget.declaration.path declaringScope
      checkedTarget.declaration.repeatableScope)
  let groups ←
    model.resolveRuleBoundFixedGroupReferences declaringGroup surfaces
    |>.mapError .group
  match groups.find? fun reference =>
      reference.boundRepeatableScope != declaringScope with
  | some reference =>
      throw (.groupScopeMismatch reference.path declaringScope
        reference.boundRepeatableScope)
  | none => pure ()
  if groups.length < 2 then
    throw .needsMultipleOperands
  match ResolvedGroupReferences.firstOverlap? groups with
  | some (left, right) => throw (.overlappingOperands left right)
  | none =>
      match groups.find? ResolvedGroupReference.isRoot with
      | some root => throw (.rootOperand root.path)
      | none =>
          if groups.any fun group => group.referencesField model targetField then
            throw (.targetSelfReference targetField)
          else
            pure { checkedTarget, groups }

inductive RepeatableNumberFixedGroupCountFault where
  | targetRows (cause : ActualRowEnvironmentError)
  | targetEnvironment (cause : EnvBindingError)
  | group (cause : CheckedGroupPresenceError)
  deriving Repr, DecidableEq

structure RepeatableNumberFixedGroupCountOutcome where
  targetField : CellAddr
  outcome : NumericTargetOutcome
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberFixedGroupCountComputation

private def readGroup (input : CheckedDocument model) (environment : Env)
    (reference : ResolvedGroupReference) :
    Except RepeatableNumberFixedGroupCountFault GroupCountOperandReading := do
  let group ← input.groupPresenceInput reference.path environment .fullyRelevant false
    |>.mapError .group
  pure (.fixed
    (group.descendantCells.map (observeCell .computation))
    group.hasInstantiatedRow)

/-- Count each fixed child only inside the current target environment, preserving document row
order. Over-limit target rows clear; every in-capacity row stores the integral count. -/
def execute (operation : CheckedRepeatableNumberFixedGroupCountComputation model)
    (input : CheckedDocument model) :
    Except RepeatableNumberFixedGroupCountFault
      (List RepeatableNumberFixedGroupCountOutcome) :=
  let field := operation.checkedTarget.targetField
  let scope := operation.checkedTarget.declaration.repeatableScope
  let at? (outcome : NumericTargetOutcome) (environment : Env) :
      Except RepeatableNumberFixedGroupCountFault
        RepeatableNumberFixedGroupCountOutcome :=
    match environment.pathForScope scope with
    | .error cause => .error (.targetEnvironment cause)
    | .ok path => .ok { targetField := { field, path }, outcome }
  let produce (environment : Env) := do
    let readings ← operation.groups.mapM (readGroup input environment)
    let count := numberOfFilledGroupsForComputationOperands readings
    let stored := (StoredNumber.fromComputed count 0).2
    at? (.accepted stored) environment
  input.computationRowOutcomes scope .targetRows (at? .noValue) produce

end CheckedRepeatableNumberFixedGroupCountComputation

end A12Kernel
