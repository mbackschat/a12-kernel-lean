import A12Kernel.Elaboration.ComputationNumericGuard
import A12Kernel.Elaboration.ComputationAlternativeAdmission
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Semantics.StringAlternatives

/-! # Checked nonrepeatable String computation tables

This capsule certifies an already-resolved, nonempty String table against one validated flat model. A sole row may omit its precondition; every row in a multi-row source table must retain an admitted condition tree. Rows reuse the existing checked String operation, first-match selector, declaration-owned target policy, and resolved evaluator. The table stores one target and policy rather than repeating them per row, while every row retains its computation declaration group until the runtime-only projection.

Guard admission belongs to `ComputationCondition.wellFormedBool`, including scalar presence and numeric comparisons at fixed scope. The certifier joins an optional common precondition onto every row's own guard. Scheduling, result projection, application, and validation remain separate.
-/

namespace A12Kernel

/-- One row after its checked operation has been consolidated into the table's shared target. -/
structure CheckedStringComputationAlternative (model : FlatModel) (target : FieldId) where
  declaringGroup : GroupPath
  precondition : Option (CheckedComputationCondition model)
  expression : CheckedStringExpr model
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  guardWellFormed : precondition.all (·.wellFormedBool) = true
  guardExcludesTarget : precondition.all
    (fun guard => !guard.forbidsTarget target) = true
  expressionExcludesTarget : expression.core.referencesField target = false

namespace CheckedStringComputationAlternative

def toResolved (alternative : CheckedStringComputationAlternative model target) : CheckedComputationAlternative model StringExpr where
  precondition := alternative.precondition
  operation := alternative.expression.core

end CheckedStringComputationAlternative

/-- A nonempty table with one model-owned nonrepeatable String target and policy. -/
structure CheckedStringComputationTable (model : FlatModel) where
  targetField : FieldId
  targetPolicy : StringFieldPolicy
  first : CheckedStringComputationAlternative model targetField
  remaining : List (CheckedStringComputationAlternative model targetField)
  modelWellFormed : model.validate.isOk = true
  targetAdmitted : model.admitsStringComputationTarget targetField targetPolicy = true

inductive StringComputationTableError where
  | empty
  | unguardedAlternative (alternative : Nat)
  | targetMismatch (alternative : Nat) (expected actual : FieldId)
  | guardNotAdmitted (alternative : Nat)
  | guardTargetReference (alternative : Nat)
  deriving Repr, DecidableEq

/-- Project the measured guard refusals: a guard reading the table's own target draws the class a
read of the target draws anywhere in a computation
([`spec/09`](../../spec/09-computations.md) §1), measured in a sole and a later alternative, and an
unguarded alternative among several draws `MVK_ERROR_EMPTY_PRECONDITION` on a String target as on a
Number one ([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-10-02a-alternative-walk)). The structural
refusals claim no class. -/
def StringComputationTableError.diagnostic? : StringComputationTableError → Option KernelStaticDiagnostic
  | .guardTargetReference _ => some .errorReferenceToCalculatedField
  | .unguardedAlternative _ => some .errorEmptyPrecondition
  | .empty | .targetMismatch _ _ _ | .guardNotAdmitted _ => none

/-- Certify one row with `commonPrecondition` joined onto its own guard. Its guardedness is judged on
the own guard alone, and the joined guard's read of the target refuses at the first row reached, which
is where the walk judges the common precondition. -/
private def certifyStringComputationAlternative
    (target : FieldId) (alternativeIndex : Nat) (guardRequired : Bool)
    (commonPrecondition : Option (CheckedComputationCondition model))
    (own : CheckedComputationAlternative model (CheckedStringComputationOperation model)) :
    Except StringComputationTableError (CheckedStringComputationAlternative model target) := do
  if guardRequired && own.precondition.isNone then
    throw (.unguardedAlternative alternativeIndex)
  let alternative : CheckedComputationAlternative model (CheckedStringComputationOperation model) :=
    { own with precondition := CheckedComputationCondition.withCommon commonPrecondition own.precondition }
  if hSameTarget : alternative.operation.targetField = target then
    if hGuard : alternative.precondition.all (·.wellFormedBool) = true then
      if hTarget : alternative.precondition.all
          (fun guard => !guard.forbidsTarget target) = true then
        pure {
          declaringGroup := alternative.operation.declaringGroup
          precondition := alternative.precondition
          expression := alternative.operation.expression
          declaringGroupValid := alternative.operation.declaringGroupValid
          guardWellFormed := hGuard
          guardExcludesTarget := hTarget
          expressionExcludesTarget := by simpa [hSameTarget] using
            alternative.operation.targetNotReferenced
        }
      else
        throw (.guardTargetReference alternativeIndex)
    else
      throw (.guardNotAdmitted alternativeIndex)
  else
    throw (.targetMismatch alternativeIndex target alternative.operation.targetField)

private def certifyStringComputationAlternatives
    (target : FieldId) (guardRequired : Bool) (commonPrecondition : Option (CheckedComputationCondition model)) :
    Nat → List (CheckedComputationAlternative model (CheckedStringComputationOperation model)) →
      Except StringComputationTableError (List (CheckedStringComputationAlternative model target))
  | _, [] => pure []
  | alternativeIndex, alternative :: remaining => do
      let checked ← certifyStringComputationAlternative target alternativeIndex
        guardRequired commonPrecondition alternative
      let checkedRemaining ← certifyStringComputationAlternatives target guardRequired
        commonPrecondition (alternativeIndex + 1) remaining
      pure (checked :: checkedRemaining)

/-- Consolidate a nonempty list of already-checked String operations into one model-certified table. Alternative positions are one-based.

    A common precondition guards no alternative: several alternatives without their own refuse as
    unguarded, and its reads of the target are judged once, at the first row
    ([checkpoint](../../docs/sources/computation-scheduling-probes.md#src-self-read-alternative-walk)). -/
def certifyStringComputationTable
    (alternatives : List (CheckedComputationAlternative model
      (CheckedStringComputationOperation model)))
    (commonPrecondition : Option (CheckedComputationCondition model) := none) :
    Except StringComputationTableError (CheckedStringComputationTable model) :=
  match alternatives with
  | [] => .error .empty
  | first :: remaining => do
      let target := first.operation.targetField
      let policy := first.operation.targetPolicy
      let guardRequired := !remaining.isEmpty
      let checkedFirst ← certifyStringComputationAlternative target 1
        guardRequired commonPrecondition first
      let checkedRemaining ← certifyStringComputationAlternatives target
        guardRequired commonPrecondition 2 remaining
      pure {
        targetField := target
        targetPolicy := policy
        first := checkedFirst
        remaining := checkedRemaining
        modelWellFormed := first.operation.expression.modelWellFormed
        targetAdmitted := first.operation.targetAdmitted
      }

inductive StringComputationTableElabErrorOf (OperationError : Type) where
  | operation (alternative : Nat) (error : OperationError)
  | table (error : StringComputationTableError)
  deriving Repr, DecidableEq

abbrev StringComputationTableElabError := StringComputationTableElabErrorOf StringComputationElabError

def StringComputationTableElabError.diagnostic? :
    StringComputationTableElabError → Option KernelStaticDiagnostic
  | .operation _ error => error.targetDiagnostic?
  | .table error => error.diagnostic?

/-- Certify each authored row's operation attempt without moving a later lowering refusal ahead of
an earlier operation refusal. Non-target-read refusals precede own guardedness and target reads,
using the same alternative walk as Number
([inbound](../../docs/sources/inbound-handbacks.md#inbound-2026-10-02a-alternative-walk)). Guards are
already resolved; the common guard remains separate until the table certifies. The caller identifies
only the operation's typed target-read refusal for the deferred stage. -/
def certifyStringComputationTableFromAttempts {OperationError : Type} (model : FlatModel)
    (target : FieldId)
    (alternatives : List (Option (CheckedComputationCondition model) ×
      Except OperationError (CheckedStringComputationOperation model)))
    (operationIsTargetRead : OperationError → Bool)
    (commonPrecondition : Option (CheckedComputationCondition model) := none) :
    Except (StringComputationTableElabErrorOf OperationError) (CheckedStringComputationTable model) :=
  let elaborated := alternatives.map fun (precondition, operation) =>
    ((.ok precondition : Except Empty _), operation)
  let refusal? := ComputationAlternative.admissionRefusal? elaborated
    (fun own => (CheckedComputationCondition.withCommon commonPrecondition own).all (·.wellFormedBool))
    (·.forbidsTarget target)
    operationIsTargetRead
    (commonPrecondition.any (·.forbidsTarget target))
  match refusal? with
  | some refusal => .error (match refusal with
      | .precondition _ error => nomatch error
      | .operation index error => .operation index error
      | .guardNotAdmitted index => .table (.guardNotAdmitted index)
      | .unguardedAlternative index => .table (.unguardedAlternative index)
      | .guardTargetReference index => .table (.guardTargetReference index))
  | none => do
      let checked ← elaborated.zipIdx.mapM fun ((guard, result), index) => do
        let precondition := match guard with
          | .ok precondition => precondition
          | .error error => nomatch error
        let operation ← result.mapError (.operation (index + 1))
        pure { precondition, operation }
      (certifyStringComputationTable checked commonPrecondition).mapError .table

/-- Elaborate String expressions into per-row operation attempts, then apply the shared admission
walk before assembling the checked table. -/
def elaborateStringComputationTable (model : FlatModel) (declaringGroup : GroupPath)
    (target : FieldId)
    (alternatives : List (Option (CheckedComputationCondition model) × StringExpr SurfaceFieldPath String))
    (commonPrecondition : Option (CheckedComputationCondition model) := none) :
    Except StringComputationTableElabError (CheckedStringComputationTable model) :=
  certifyStringComputationTableFromAttempts model target
    (alternatives.map fun (precondition, expression) =>
      (precondition, elaborateStringComputationOperation model declaringGroup target expression))
    (fun | .targetSelfReference _ => true | _ => false) commonPrecondition

inductive CheckedStringComputationFault where
  | operation (fault : StringComputationFault)
  | guard (fault : CheckedComputationConditionError)
  deriving Repr, DecidableEq

namespace CheckedStringComputationTable

/-- The checked alternatives in their authored encounter order. -/
def selectableAlternatives (table : CheckedStringComputationTable model) :
    List (CheckedStringComputationAlternative model table.targetField) :=
  table.first :: table.remaining

/-- Preserve each alternative's computation declaration group in authored encounter order. Runtime
evaluation does not need placement, but Analyze and Transform consumers do. -/
def declaringGroups (table : CheckedStringComputationTable model) : List GroupPath :=
  table.selectableAlternatives.map (·.declaringGroup)

/-- Erase only model certificates, retaining target, policy, guard order, and expression trees exactly. Prior target state is supplied by the later result-projection boundary. -/
def toResolved (table : CheckedStringComputationTable model) (prior : PriorStringTarget) : StringAlternativeComputation (CheckedComputationCondition model) where
  targetField := table.targetField
  alternatives := table.selectableAlternatives.map (·.toResolved)
  targetPolicy := table.targetPolicy
  targetRegime := ((model.lookupUniqueId table.targetField).toOption.map (·.stringTargetRegime)).getD .ordinary
  prior

/-- Evaluate through the sole resolved first-match owner and an explicitly prepared target matcher. Selection completes before the chosen String expression can produce no value, rejection, or poison. -/
def evaluateOutcomeWithPattern (table : CheckedStringComputationTable model)
    (wholeValueMatches? : Option (String → Bool)) (context : StringComputationContext)
    (guardContext : ScalarComputationContext) (indexColumn? : Option SemanticIndexColumnReader := none) :
    Except CheckedStringComputationFault StringTargetOutcome :=
  match (table.toResolved .empty).evaluateOutcomeWithGuard
      (fun condition => condition.evalChecked guardContext indexColumn?)
      CheckedStringComputationFault.guard CheckedStringComputationFault.operation wholeValueMatches? context with
  | .error (.guard error) => if error.isValueFailure then .ok .invalidNoValue else .error (.guard error)
  | result => result

end CheckedStringComputationTable

end A12Kernel
