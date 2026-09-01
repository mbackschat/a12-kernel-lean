import A12Kernel.Elaboration.ComputationCondition
import A12Kernel.Elaboration.StringComputation
import A12Kernel.Semantics.StringAlternatives

/-! # Checked nonrepeatable String computation tables

This capsule certifies an already-resolved, nonempty String table against one validated flat model. A sole row may omit its precondition; every row in a multi-row source table must retain a direct-presence condition tree. Rows reuse the existing checked String operation, first-match selector, declaration-owned target policy, and resolved evaluator. The table stores one target and policy rather than repeating them per row, while every row retains its computation declaration group until the runtime-only projection.

The guard fragment admits any nonrepeatable scalar declaration, including raw String presence, but no repeatable reference. Common-precondition distribution has already happened before this boundary. Scheduling, result projection, application, and validation remain separate.
-/

namespace A12Kernel

/-- One row after its checked operation has been consolidated into the table's shared target. -/
structure CheckedStringComputationAlternative (model : FlatModel) (target : FieldId) where
  declaringGroup : GroupPath
  precondition : Option ComputationCondition
  expression : CheckedStringExpr model
  declaringGroupValid : GroupPath.isValid declaringGroup = true
  guardWellFormed : precondition.all (·.wellFormedBool model) = true
  guardExcludesTarget : precondition.all
    (fun guard => !guard.referencesField target) = true
  expressionExcludesTarget : expression.core.referencesField target = false

namespace CheckedStringComputationAlternative

def toResolved (alternative : CheckedStringComputationAlternative model target) : ComputationAlternative StringExpr where
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

private def certifyStringComputationAlternative
    (target : FieldId) (alternativeIndex : Nat) (guardRequired : Bool)
    (alternative : ComputationAlternative (CheckedStringComputationOperation model)) :
    Except StringComputationTableError (CheckedStringComputationAlternative model target) := do
  if hSameTarget : alternative.operation.targetField = target then
    if guardRequired && alternative.precondition.isNone then
      throw (.unguardedAlternative alternativeIndex)
    else if hGuard : alternative.precondition.all (·.wellFormedBool model) = true then
      if hTarget : alternative.precondition.all
          (fun guard => !guard.referencesField target) = true then
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
    (target : FieldId) (guardRequired : Bool) :
    Nat → List (ComputationAlternative (CheckedStringComputationOperation model)) →
      Except StringComputationTableError (List (CheckedStringComputationAlternative model target))
  | _, [] => pure []
  | alternativeIndex, alternative :: remaining => do
      let checked ← certifyStringComputationAlternative target alternativeIndex
        guardRequired alternative
      let checkedRemaining ← certifyStringComputationAlternatives target guardRequired
        (alternativeIndex + 1) remaining
      pure (checked :: checkedRemaining)

/-- Consolidate a nonempty list of already-checked String operations into one model-certified table. Alternative positions are one-based. -/
def certifyStringComputationTable
    (alternatives : List (ComputationAlternative
      (CheckedStringComputationOperation model))) :
    Except StringComputationTableError (CheckedStringComputationTable model) :=
  match alternatives with
  | [] => .error .empty
  | first :: remaining => do
      let target := first.operation.targetField
      let policy := first.operation.targetPolicy
      let guardRequired := !remaining.isEmpty
      let checkedFirst ← certifyStringComputationAlternative target 1
        guardRequired first
      let checkedRemaining ← certifyStringComputationAlternatives target
        guardRequired 2 remaining
      pure {
        targetField := target
        targetPolicy := policy
        first := checkedFirst
        remaining := checkedRemaining
        modelWellFormed := first.operation.expression.modelWellFormed
        targetAdmitted := first.operation.targetAdmitted
      }

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
def toResolved (table : CheckedStringComputationTable model) (prior : PriorStringTarget) : StringAlternativeComputation where
  targetField := table.targetField
  alternatives := table.selectableAlternatives.map (·.toResolved)
  targetPolicy := table.targetPolicy
  prior

/-- Evaluate through the sole resolved first-match owner and an explicitly prepared target matcher. Selection completes before the chosen String expression can produce no value, rejection, or poison. -/
def evaluateOutcomeWithPattern (table : CheckedStringComputationTable model)
    (wholeValueMatches? : Option (String → Bool)) (context : StringComputationContext) :
    Except StringComputationFault StringTargetOutcome :=
  (table.toResolved .empty).evaluateOutcomeWithPattern wholeValueMatches? context

end CheckedStringComputationTable

end A12Kernel
