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

/-- Project the measured alternative classes: a guard reading the table's own target draws the class a
read of the target draws anywhere in a computation ([`spec/09`](../../../spec/09-computations.md)
§1), and an unguarded alternative among several draws `MVK_ERROR_EMPTY_PRECONDITION`
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)).
The certifier meets both in authored order, which is the order the Kernel reports them in. The
structural refusals claim no class. -/
def NumericComputationTableError.diagnostic? : NumericComputationTableError → Option KernelStaticDiagnostic
  | .guardTargetReference _ => some .errorReferenceToCalculatedField
  | .unguardedAlternative _ => some .errorEmptyPrecondition
  | .empty | .targetMismatch _ _ _ | .targetPolicyMismatch _ | .guardNotAdmitted _ => none

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

/-- Consolidate already-checked Number operations without reordering their guards. Alternative positions
are one-based. Every guard's admission is asked before any alternative's own class, as the Kernel asks a
guard's name ahead of an unguarded alternative wherever either stands
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)). -/
def certifyNumericComputationTable
    (alternatives : List (ComputationAlternative
      (CheckedNumericTargetComputationOperation model))) :
    Except NumericComputationTableError (CheckedNumericComputationTable model) :=
  match alternatives with
  | [] => .error .empty
  | first :: remaining => do
      if let some (_, index) := (first :: remaining).zipIdx.find? fun (alternative, _) =>
          !alternative.precondition.all (·.wellFormedBool model) then
        throw (.guardNotAdmitted (index + 1))
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

/-- The Kernel class of a whole computation's refusal, through each failure's own projection. Where
the Kernel reports several codes this is the first of them; the reads of the target it reports once
per occurrence are not counted. -/
def diagnostic? : NumericComputationTableElabError → Option KernelStaticDiagnostic
  | .operation _ error => error.diagnostic?
  | .table error => error.diagnostic?

end NumericComputationTableElabError

/-- Elaborate a whole Number computation from its authored alternatives, each an already-resolved
precondition beside an authored operation, in the two stages the Kernel asks
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)).

First each alternative in authored order is asked everything but a read of its target: its guard's
admission, then its operation's names, authoring, kinds and scale. The first alternative failing one
of them reports that refusal alone, whatever any other alternative holds, so neither a computation-wide
names stage nor a computation-wide scale stage exists. Then the alternatives' own classes are asked in
authored order: an unguarded alternative among several refuses as such, once, and its own reads of the
target go unreported, while every other alternative's guard or operation reading the target refuses as
that read. Warning suppression is the whole computation's and lifts only the scale gate.

A guard's name is resolved by the caller, so a guard that does not resolve meets this elaborator as an
unadmitted guard, asked in its alternative's place. -/
def elaborateNumericTargetComputationTable (model : FlatModel) (declaringGroup : GroupPath)
    (target : FieldId)
    (alternatives : List (Option ComputationCondition × AuthoredNumericExpr SurfaceNumericAtom))
    (suppressExactScaleWarning : Bool := false) :
    Except NumericComputationTableElabError (CheckedNumericComputationTable model) :=
  let elaborated := alternatives.zipIdx.map fun ((precondition, expression), index) =>
    (index + 1, precondition,
      elaborateNumericTargetComputationOperation model declaringGroup target expression
        suppressExactScaleWarning)
  let otherRefusal? := elaborated.findSome? fun (index, precondition, result) =>
    if !precondition.all (·.wellFormedBool model) then
      some (.table (.guardNotAdmitted index))
    else
      match result with
      | .error (.targetSelfReference _) | .ok _ => none
      | .error error => some (.operation index error)
  let several := alternatives.length > 1
  let alternativeRefusal? := elaborated.findSome? fun (index, precondition, result) =>
    match precondition with
    | none => if several then some (.table (.unguardedAlternative index)) else
        match result with
        | .error error => some (.operation index error)
        | .ok _ => none
    | some guard =>
        if guard.referencesField target then some (.table (.guardTargetReference index)) else
          match result with
          | .error error => some (.operation index error)
          | .ok _ => none
  match otherRefusal? <|> alternativeRefusal? with
  | some refusal => .error refusal
  | none => do
      let checked ← elaborated.mapM fun (index, precondition, result) =>
        result.mapError (.operation index) |>.map fun operation => { precondition, operation }
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
