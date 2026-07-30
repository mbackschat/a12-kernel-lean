import A12Kernel.Elaboration.ComputationCondition
import A12Kernel.Elaboration.NumericComputation.Target

/-! # Checked Number computation tables

This capsule consolidates a nonempty guarded table of already-checked Number target operations. Every row must retain the same target and complete target policy. Selection reuses the shared first-match owner and delegates only the selected operation to the existing scalar Numeric evaluator.
-/

namespace A12Kernel

/-- One guarded Number row certified against the table's shared target and target policy. The complete checked operation is retained because assignment-scale admission and warning suppression are target-specific. -/
structure CheckedNumericComputationAlternative (model : FlatModel)
    (target : FieldId) (policy : NumericTargetPolicy) where
  precondition : ComputationCondition
  operation : CheckedNumericTargetComputationOperation model
  targetMatches : operation.operation.core.target.id = target
  policyMatches : operation.policy = policy
  guardWellFormed : precondition.WellFormed model
  guardExcludesTarget : precondition.referencesField target = false

namespace CheckedNumericComputationAlternative

def toSelectable (alternative :
    CheckedNumericComputationAlternative model target policy) :
    ComputationAlternative (CheckedNumericTargetComputationOperation model) where
  precondition := alternative.precondition
  operation := alternative.operation

end CheckedNumericComputationAlternative

/-- A nonempty guarded Number table with one model-owned target and complete policy. -/
structure CheckedNumericComputationTable (model : FlatModel) where
  targetField : FieldId
  targetPolicy : NumericTargetPolicy
  first : CheckedNumericComputationAlternative model targetField targetPolicy
  remaining :
    List (CheckedNumericComputationAlternative model targetField targetPolicy)

inductive NumericComputationTableError where
  | empty
  | targetMismatch (alternative : Nat) (expected actual : FieldId)
  | targetPolicyMismatch (alternative : Nat)
  | guardNotAdmitted (alternative : Nat)
  | guardTargetReference (alternative : Nat)
  deriving Repr, DecidableEq

private def certifyNumericComputationAlternative
    (target : FieldId) (policy : NumericTargetPolicy) (alternativeIndex : Nat)
    (alternative : ComputationAlternative
      (CheckedNumericTargetComputationOperation model)) :
    Except NumericComputationTableError
      (CheckedNumericComputationAlternative model target policy) := do
  if hTarget : alternative.operation.operation.core.target.id = target then
    if hPolicy : alternative.operation.policy = policy then
      if hGuard : alternative.precondition.wellFormedBool model = true then
        if hGuardTarget :
            alternative.precondition.referencesField target = false then
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
      let checkedFirst ←
        certifyNumericComputationAlternative target policy 1 first
      let checkedRemaining ← remaining.zipIdx.mapM fun (alternative, index) =>
        certifyNumericComputationAlternative target policy (index + 2)
          alternative
      pure {
        targetField := target
        targetPolicy := policy
        first := checkedFirst
        remaining := checkedRemaining
      }

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

/-- Select first through computation-phase scalar guards, then evaluate only that checked operation. Repeatable operands retain the existing explicit scalar-context fault. -/
def evaluate (table : CheckedNumericComputationTable model)
    (context : ScalarComputationContext) :
    Except NumericComputationFault NumericTargetCheckResult :=
  match ComputationAlternative.selectFirst
      table.selectableAlternatives context with
  | .noMatch => pure (.supported .noValue)
  | .poison cause => pure (.supported (.inheritedPoison cause))
  | .selected operation => operation.evaluate context

end CheckedNumericComputationTable

end A12Kernel
