import A12Kernel.Elaboration.ComputationCondition
import A12Kernel.Elaboration.NumericComputation.Target

/-! # Checked Number computation tables

This capsule consolidates a nonempty table of already-checked Number target operations. A sole source row may omit its precondition; every row in a multi-row source table must be guarded. Every row retains the same target and complete target policy. Selection reuses the shared first-match owner and delegates only the selected operation to the existing scalar Numeric evaluator.
-/

namespace A12Kernel

/-- One Number row certified against the table's shared target and target policy. The complete checked operation is retained because assignment-scale admission and warning suppression are target-specific. -/
structure CheckedNumericComputationAlternative (model : FlatModel)
    (target : FieldId) (policy : NumericTargetPolicy) where
  precondition : Option ComputationCondition
  operation : CheckedNumericTargetComputationOperation model
  targetMatches : operation.operation.core.target.id = target
  policyMatches : operation.policy = policy
  guardWellFormed : precondition.all (·.wellFormedBool model) = true
  guardExcludesTarget : precondition.all
    (fun guard => !guard.referencesField target) = true

namespace CheckedNumericComputationAlternative

def toSelectable (alternative :
    CheckedNumericComputationAlternative model target policy) :
    ComputationAlternative (CheckedNumericTargetComputationOperation model) where
  precondition := alternative.precondition
  operation := alternative.operation

end CheckedNumericComputationAlternative

/-- A nonempty Number table with one model-owned target and complete policy. -/
structure CheckedNumericComputationTable (model : FlatModel) where
  targetField : FieldId
  targetPolicy : NumericTargetPolicy
  first : CheckedNumericComputationAlternative model targetField targetPolicy
  remaining :
    List (CheckedNumericComputationAlternative model targetField targetPolicy)

inductive NumericComputationTableError where
  | empty
  | unguardedAlternative (alternative : Nat)
  | targetMismatch (alternative : Nat) (expected actual : FieldId)
  | targetPolicyMismatch (alternative : Nat)
  | guardNotAdmitted (alternative : Nat)
  | guardTargetReference (alternative : Nat)
  deriving Repr, DecidableEq

/-- Project the measured guard refusal: a guard reading the table's own target draws the class a
read of the target draws anywhere in a computation
([`spec/09`](../../../spec/09-computations.md) §1), measured in a sole and a later alternative. The
structural refusals claim no class. -/
def NumericComputationTableError.diagnostic? : NumericComputationTableError → Option KernelStaticDiagnostic
  | .guardTargetReference _ => some .errorReferenceToCalculatedField
  | .empty | .unguardedAlternative _ | .targetMismatch _ _ _ | .targetPolicyMismatch _
  | .guardNotAdmitted _ => none

private def certifyNumericComputationAlternative
    (target : FieldId) (policy : NumericTargetPolicy) (alternativeIndex : Nat)
    (guardRequired : Bool)
    (alternative : ComputationAlternative
      (CheckedNumericTargetComputationOperation model)) :
    Except NumericComputationTableError
      (CheckedNumericComputationAlternative model target policy) := do
  if hTarget : alternative.operation.operation.core.target.id = target then
    if hPolicy : alternative.operation.policy = policy then
      if guardRequired && alternative.precondition.isNone then
        throw (.unguardedAlternative alternativeIndex)
      else if hGuard : alternative.precondition.all (·.wellFormedBool model) = true then
        if hGuardTarget : alternative.precondition.all
            (fun guard => !guard.referencesField target) = true then
          pure {
            precondition := alternative.precondition
            operation := alternative.operation
            targetMatches := hTarget
            policyMatches := hPolicy
            guardWellFormed := hGuard
            guardExcludesTarget := hGuardTarget
          }
        else
          throw (.guardTargetReference alternativeIndex)
      else
        throw (.guardNotAdmitted alternativeIndex)
    else
      throw (.targetPolicyMismatch alternativeIndex)
    else
      throw (.targetMismatch alternativeIndex target
      alternative.operation.operation.core.target.id)

/-- Consolidate already-checked Number operations without reordering their guards. Alternative positions are one-based. -/
def certifyNumericComputationTable
    (alternatives : List (ComputationAlternative
      (CheckedNumericTargetComputationOperation model))) :
    Except NumericComputationTableError (CheckedNumericComputationTable model) :=
  match alternatives with
  | [] => .error .empty
  | first :: remaining => do
      let target := first.operation.operation.core.target.id
      let policy := first.operation.policy
      let guardRequired := !remaining.isEmpty
      let checkedFirst ←
        certifyNumericComputationAlternative target policy 1 guardRequired first
      let checkedRemaining ← remaining.zipIdx.mapM fun (alternative, index) =>
        certifyNumericComputationAlternative target policy (index + 2) guardRequired
          alternative
      pure {
        targetField := target
        targetPolicy := policy
        first := checkedFirst
        remaining := checkedRemaining
      }

/-- Why a whole Number computation is refused: one alternative's operation, numbered from 1, or the
table assembled from the checked operations. -/
inductive NumericComputationTableElabError where
  | operation (alternative : Nat) (error : NumericComputationElabError)
  | table (error : NumericComputationTableError)
  deriving Repr, DecidableEq

namespace NumericComputationTableElabError

/-- The Kernel class of a whole computation's refusal, through each failure's own projection. -/
def diagnostic? : NumericComputationTableElabError → Option KernelStaticDiagnostic
  | .operation _ error => error.targetDiagnostic?
  | .table error => error.diagnostic?

end NumericComputationTableElabError

/-- Elaborate a whole Number computation from its authored alternatives, each a precondition beside an
operation. The Kernel asks every alternative's other gates before any read of the target, so a
self-read in one alternative beside a scale mismatch, a second unbraced division or an unresolved
name in another draws that other class
([checkpoint](../../../docs/sources/evaluation-and-application-routes.md#src-join-operators-and-guards)).
An operation refuses its own self-read only past its own gates, so the first refusal that is no
self-read, in authored order, answers first, then the first self-read, then the table's checks,
among them a guard's self-read. Where an unguarded alternative and a self-read meet, the Kernel
reports both ([`spec/09`](../../../spec/09-computations.md) §1) and this reports one: an operation's
self-read, or the unguarded alternative ahead of a guard's. The order among two alternatives' other refusals is
authored order here, which only one alternative failing ever measures. -/
def elaborateNumericTargetComputationTable (model : FlatModel) (declaringGroup : GroupPath)
    (target : FieldId)
    (alternatives : List (Option ComputationCondition × AuthoredNumericExpr SurfaceNumericAtom)) :
    Except NumericComputationTableElabError (CheckedNumericComputationTable model) :=
  let elaborated := alternatives.zipIdx.map fun ((precondition, expression), index) =>
    (index + 1, precondition,
      elaborateNumericTargetComputationOperation model declaringGroup target expression)
  let refusal? (selfRead : Bool) := elaborated.findSome? fun (index, _, result) =>
    match result with
    | .error error =>
        if (error matches .targetSelfReference _) == selfRead then some (index, error) else none
    | .ok _ => none
  match refusal? false, refusal? true with
  | some (index, error), _ | none, some (index, error) => .error (.operation index error)
  | none, none =>
      let checked := elaborated.filterMap fun (_, precondition, result) =>
        result.toOption.map fun operation => { precondition, operation }
      (certifyNumericComputationTable checked).mapError .table

namespace CheckedNumericComputationTable

/-- Retain every checked row in authored order for same-target assembly. -/
def checkedAlternatives (table : CheckedNumericComputationTable model) :
    List (CheckedNumericComputationAlternative
      model table.targetField table.targetPolicy) :=
  table.first :: table.remaining

def selectableAlternatives (table : CheckedNumericComputationTable model) :
    List (ComputationAlternative
      (CheckedNumericTargetComputationOperation model)) :=
  table.checkedAlternatives.map (·.toSelectable)

/-- Preserve each row's computation declaration group in authored order. Runtime selection does not
consume placement, but Analyze and Transform consumers do. -/
def declaringGroups (table : CheckedNumericComputationTable model) : List GroupPath :=
  table.checkedAlternatives.map (·.operation.operation.declaringGroup)

/-- Select first through computation-phase scalar guards, then evaluate only that checked operation. Repeatable operands retain the existing explicit scalar-context fault. -/
def evaluate (table : CheckedNumericComputationTable model)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericTargetCheckResult :=
  match ComputationAlternative.selectFirst
      table.selectableAlternatives context with
  | .noMatch => pure (.supported .noValue)
  | .poison cause => pure (.supported (.inheritedPoison cause))
  | .selected operation => operation.evaluate context

/-- Select first through the context's scalar guards, then evaluate only that operation with its
repeatable reads, so a selected aggregate reads its rows through the context's star view. -/
def evaluateIn (table : CheckedNumericComputationTable model)
    (context : NumericComputationEvaluationContext) :
    Except NumericComputationFault NumericTargetCheckResult :=
  match ComputationAlternative.selectFirst
      table.selectableAlternatives context.scalar with
  | .noMatch => pure (.supported .noValue)
  | .poison cause => pure (.supported (.inheritedPoison cause))
  | .selected operation => operation.evaluateIn context

end CheckedNumericComputationTable

end A12Kernel
