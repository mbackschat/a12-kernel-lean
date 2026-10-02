import A12Kernel.Elaboration.ComputationCondition
import A12Kernel.Elaboration.NumericComputation.Target

/-! # Checked Number computation tables

This capsule consolidates a nonempty table of already-checked Number target operations. A sole source row may omit its precondition; every row in a multi-row source table must be guarded. Every row retains the same target and complete target policy, and every guard reads only cells one row of the target's scope binds, as the table's operations do. Selection reuses the shared first-match owner and delegates only the selected operation to the existing scalar Numeric evaluator.
-/

namespace A12Kernel

/-- One Number row certified against the table's shared target and target policy. The complete checked operation is retained because assignment-scale admission and warning suppression are target-specific. -/
structure CheckedNumericComputationAlternative (model : FlatModel)
    (target : FieldId) (policy : NumericTargetPolicy) where
  precondition : Option ComputationCondition
  operation : CheckedNumericTargetComputationOperation model
  targetMatches : operation.operation.core.target.id = target
  policyMatches : operation.policy = policy
  guardRowBound : precondition.all (·.rowBoundBool model (model.fieldRepeatableScope target)) = true
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
    (admitted : AdmittedComputationAlternative
      (·.rowBoundBool model (model.fieldRepeatableScope target))
      (CheckedNumericTargetComputationOperation model)) :
    Except NumericComputationTableError
      (CheckedNumericComputationAlternative model target policy) := do
  let alternative := admitted.val
  if hTarget : alternative.operation.operation.core.target.id = target then
    if hPolicy : alternative.operation.policy = policy then
      if guardRequired && alternative.precondition.isNone then
        throw (.unguardedAlternative alternativeIndex)
      else if hGuardTarget : alternative.precondition.all
          (fun guard => !guard.referencesField target) = true then
        pure {
          precondition := alternative.precondition
          operation := alternative.operation
          targetMatches := hTarget
          policyMatches := hPolicy
          guardRowBound := admitted.property
          guardExcludesTarget := hGuardTarget
        }
      else
        throw (.guardTargetReference alternativeIndex)
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
      let target := first.operation.operation.core.target.id
      let (first, remaining) ←
        (ComputationAlternative.admitGuards
          (·.rowBoundBool model (model.fieldRepeatableScope target)) first remaining).mapError
          .guardNotAdmitted
      let policy := first.val.operation.policy
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

/-- Why a whole Number computation is refused: one alternative's authored guard or operation, numbered
from 1, or the table assembled from the checked operations. -/
inductive NumericComputationTableElabError where
  | precondition (alternative : Nat) (error : ResolveError)
  | operation (alternative : Nat) (error : NumericComputationElabError)
  | table (error : NumericComputationTableError)
  deriving Repr, DecidableEq

namespace NumericComputationTableElabError

/-- The Kernel class of a whole computation's refusal, through each failure's own projection. Where
the Kernel reports several codes this is the first of them; the reads of the target it reports once
per occurrence are not counted. -/
def diagnostic? : NumericComputationTableElabError → Option KernelStaticDiagnostic
  | .precondition _ error => error.diagnostic?
  | .operation _ error => error.diagnostic?
  | .table error => error.diagnostic?

end NumericComputationTableElabError

/-- Elaborate a whole Number computation from its authored alternatives, each a precondition resolution
already attempted beside an authored operation, in the two stages the Kernel asks
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-join-operators-and-guards)).

First each alternative in authored order is asked everything but a read of its target: its guard's
names and admission, then its operation's names, authoring, kinds and scale. The first alternative
failing one of them reports that refusal alone, whatever any other alternative holds, so neither a
computation-wide names stage nor a computation-wide scale stage exists. A guard's name answers ahead of
its own operation's classes, as the joined text puts the precondition first
([checkpoint](../../../docs/sources/computation-scheduling-probes.md#src-computation-precondition-names)).
Then the alternatives' own classes are asked in authored order: an unguarded alternative among several
refuses as such, once, and its own reads of the target go unreported, while every other alternative's
guard or operation reading the target refuses as that read. Warning suppression is the whole
computation's and lifts only the scale gate. -/
private def elaborateNumericTargetComputationTableWith (model : FlatModel) (declaringGroup : GroupPath)
    (target : FieldId)
    (alternatives : List (Except ResolveError (Option ComputationCondition) ×
      AuthoredNumericExpr SurfaceNumericComputationAtom))
    (suppressExactScaleWarning : Bool) (targetScope : ComputationTargetScope) :
    Except NumericComputationTableElabError (CheckedNumericComputationTable model) :=
  let elaborated := alternatives.zipIdx.map fun ((guard, expression), index) =>
    (index + 1, guard,
      elaborateCompleteNumericTargetComputationOperation model declaringGroup target expression
        suppressExactScaleWarning targetScope)
  let otherRefusal? := elaborated.findSome? fun (index, guard, result) =>
    match guard with
    | .error error => some (.precondition index error)
    | .ok precondition =>
        if !precondition.all (·.rowBoundBool model (model.fieldRepeatableScope target)) then
          some (.table (.guardNotAdmitted index))
        else
          match result with
          | .error (.targetSelfReference _) | .ok _ => none
          | .error error => some (.operation index error)
  let several := alternatives.length > 1
  let alternativeRefusal? := elaborated.findSome? fun (index, guard, result) =>
    match guard with
    | .error error => some (.precondition index error)
    | .ok none => if several then some (.table (.unguardedAlternative index)) else
        match result with
        | .error error => some (.operation index error)
        | .ok _ => none
    | .ok (some precondition) =>
        if precondition.referencesField target then some (.table (.guardTargetReference index)) else
          match result with
          | .error error => some (.operation index error)
          | .ok _ => none
  match otherRefusal? <|> alternativeRefusal? with
  | some refusal => .error refusal
  | none => do
      let checked ← elaborated.mapM fun (index, guard, result) => do
        let precondition ← guard.mapError (.precondition index)
        let operation ← result.mapError (.operation index)
        pure { precondition, operation }
      (certifyNumericComputationTable checked).mapError .table

/-- An ordinary numeric expression as a complete computation expression, the embedding
`elaborateNumericTargetComputationOperation` applies. -/
private def AuthoredNumericExpr.asComplete (expression : AuthoredNumericExpr SurfaceNumericAtom) :
    AuthoredNumericExpr SurfaceNumericComputationAtom :=
  expression.map fun atom => .numeric atom.toNumberEntityComputationAtom

/-- Elaborate a whole Number computation over the complete computation surface, `FirstFilledValue`
and the value counts included, whose guards the caller has already resolved. A guard that names no
model field meets it as an unadmitted guard, asked in its alternative's place. `targetScope` names the
targets the caller's executor addresses: a row table only for the repeatable plan. -/
def elaborateCompleteNumericTargetComputationTable (model : FlatModel) (declaringGroup : GroupPath)
    (target : FieldId)
    (alternatives :
      List (Option ComputationCondition × AuthoredNumericExpr SurfaceNumericComputationAtom))
    (suppressExactScaleWarning : Bool := false)
    (targetScope : ComputationTargetScope := .fixed) :
    Except NumericComputationTableElabError (CheckedNumericComputationTable model) :=
  elaborateNumericTargetComputationTableWith model declaringGroup target
    (alternatives.map fun (precondition, expression) => (.ok precondition, expression))
    suppressExactScaleWarning targetScope

/-- Elaborate a whole Number computation over ordinary numeric atoms, whose guards the caller has
already resolved. -/
def elaborateNumericTargetComputationTable (model : FlatModel) (declaringGroup : GroupPath)
    (target : FieldId)
    (alternatives : List (Option ComputationCondition × AuthoredNumericExpr SurfaceNumericAtom))
    (suppressExactScaleWarning : Bool := false)
    (targetScope : ComputationTargetScope := .fixed) :
    Except NumericComputationTableElabError (CheckedNumericComputationTable model) :=
  elaborateCompleteNumericTargetComputationTable model declaringGroup target
    (alternatives.map fun (precondition, expression) => (precondition, expression.asComplete))
    suppressExactScaleWarning targetScope

/-- Elaborate a whole Number computation whose guards are authored by name, each resolved against the
target's group as the computation's operands are. -/
def elaborateNumericTargetComputationTableFromSurface (model : FlatModel) (declaringGroup : GroupPath)
    (target : FieldId)
    (alternatives : List (Option SurfaceComputationCondition × AuthoredNumericExpr SurfaceNumericAtom))
    (suppressExactScaleWarning : Bool := false)
    (targetScope : ComputationTargetScope := .fixed) :
    Except NumericComputationTableElabError (CheckedNumericComputationTable model) :=
  -- A target the model does not own fails in its operation's elaboration; its guards then resolve
  -- against the declaring group, and no measured row reaches that pairing.
  let targetGroup := ((model.lookupUniqueId target).toOption.map (·.groupPath)).getD declaringGroup
  elaborateNumericTargetComputationTableWith model declaringGroup target
    (alternatives.map fun (precondition, expression) =>
      (precondition.mapM fun authored => do
        model.validate
        model.elaborateComputationCondition declaringGroup targetGroup authored,
        expression.asComplete))
    suppressExactScaleWarning targetScope

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

/-- Select first through computation-phase scalar guards, then evaluate only that checked operation. The context's read decides which row the operands are read at: the repeatable plan supplies a row-local one. -/
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
