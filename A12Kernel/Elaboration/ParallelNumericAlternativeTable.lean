import A12Kernel.Elaboration.ParallelNumericDirectRun

/-! # Checked parallel Number alternative tables

This boundary consolidates two or more already-checked guarded parallel Number operations for one repeatable target. It reuses the shared first-selected condition scan and delegates only the selected row to the direct operation's target evaluator. Static route collection and target-row iteration remain with the next execution capsule.
-/

namespace A12Kernel

inductive ParallelNumericAlternativeTableError where
  | fewerThanTwo
  | unguarded (alternative : Nat)
  | targetMismatch (alternative : Nat) (expected actual : FieldId)
  deriving Repr, DecidableEq

/-- One guarded parallel operation certified against the table's shared target. The complete checked operation remains intact because it owns expression, routes, scale directive, and target policy. -/
structure CheckedParallelNumericAlternative (model : FlatModel)
    (target : FieldId) where
  operation : CheckedIsolatedParallelNumericDirectRun model
  precondition : ComputationCondition
  preconditionOwned : operation.precondition = some precondition
  targetMatches : operation.route.targetField = target

namespace CheckedParallelNumericAlternative

def toSelectable
    (alternative : CheckedParallelNumericAlternative model target) :
    ComputationAlternative
      (CheckedIsolatedParallelNumericDirectRun model) where
  precondition := alternative.precondition
  operation := alternative.operation

end CheckedParallelNumericAlternative

/-- One already-flattened guarded table. Two rows are stored explicitly because a singleton has its existing optional-guard owner. -/
structure CheckedParallelNumericAlternativeTable (model : FlatModel) where
  targetField : FieldId
  first : CheckedParallelNumericAlternative model targetField
  second : CheckedParallelNumericAlternative model targetField
  remaining : List (CheckedParallelNumericAlternative model targetField)

private def certifyParallelNumericAlternative
    (target : FieldId) (alternativeIndex : Nat)
    (operation : CheckedIsolatedParallelNumericDirectRun model) :
    Except ParallelNumericAlternativeTableError
      (CheckedParallelNumericAlternative model target) :=
  match guarded : operation.precondition with
  | none => .error (.unguarded alternativeIndex)
  | some precondition =>
      if targetMatches : operation.route.targetField = target then
        .ok {
          operation
          precondition
          preconditionOwned := guarded
          targetMatches
        }
      else
        .error (.targetMismatch alternativeIndex target
          operation.route.targetField)

/-- Consolidate checked rows without reordering them. Alternative positions are one-based. -/
def certifyParallelNumericAlternativeTable
    (operations : List (CheckedIsolatedParallelNumericDirectRun model)) :
    Except ParallelNumericAlternativeTableError
      (CheckedParallelNumericAlternativeTable model) :=
  match operations with
  | first :: second :: remaining => do
      let target := first.route.targetField
      let checkedFirst ← certifyParallelNumericAlternative target 1 first
      let checkedSecond ← certifyParallelNumericAlternative target 2 second
      let checkedRemaining ← remaining.zipIdx.mapM fun (operation, index) =>
        certifyParallelNumericAlternative target (index + 3) operation
      pure {
        targetField := target
        first := checkedFirst
        second := checkedSecond
        remaining := checkedRemaining
      }
  | _ => .error .fewerThanTwo

namespace CheckedParallelNumericAlternativeTable

def alternatives
    (table : CheckedParallelNumericAlternativeTable model) :
    List (CheckedParallelNumericAlternative model table.targetField) :=
  table.first :: table.second :: table.remaining

def selectableAlternatives
    (table : CheckedParallelNumericAlternativeTable model) :
    List (ComputationAlternative
      (CheckedIsolatedParallelNumericDirectRun model)) :=
  table.alternatives.map (·.toSelectable)

/-- Select through the shared computation-condition scan, then evaluate only the selected checked parallel operation. -/
def evaluate (table : CheckedParallelNumericAlternativeTable model)
    (context : ScalarComputationContext) :
    Except CheckedIsolatedParallelNumericDirectRun.ExecutionError
      NumericTargetOutcome :=
  match ComputationAlternative.selectFirst
      table.selectableAlternatives context with
  | .noMatch => .ok .noValue
  | .poison cause => .ok (.inheritedPoison cause)
  | .selected operation => operation.evaluateSelected context

def WellFormed
    (table : CheckedParallelNumericAlternativeTable model) : Prop :=
  ∀ alternative ∈ table.alternatives,
    alternative.operation.WellFormed ∧
      alternative.operation.precondition =
        some alternative.precondition ∧
      alternative.operation.route.targetField = table.targetField

end CheckedParallelNumericAlternativeTable

end A12Kernel
