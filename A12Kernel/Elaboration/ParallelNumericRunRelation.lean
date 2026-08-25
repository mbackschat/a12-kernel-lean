import A12Kernel.Elaboration.ParallelNumericRun

/-! # Dependency-enabled repeatable Number batch relation

This purpose-specific relation schedules whole checked repeatable Number tables. Its state records completed table targets separately from emitted addressed outcomes, because a structurally suppressed table may emit no rows and must still enable a dependent table. Table execution, exact addressed overlay, and rich outcomes remain owned by the existing parallel Number run.
-/

namespace A12Kernel

abbrev ParallelNumericRunBatch := FieldId × List ParallelNumericDirectOutcome

/-- Private scheduling state for successful repeatable Number table batches. -/
structure ParallelNumericTransitionState where
  completedTargets : List FieldId := []
  outcomes : List ParallelNumericDirectOutcome := []
  deriving Repr, DecidableEq

namespace ParallelNumericTransitionState

def runState (state : ParallelNumericTransitionState) :
    ParallelNumericRunState :=
  { completed := state.outcomes }

end ParallelNumericTransitionState

/-- Every plan target statically referenced by the table has completed, including an action-free completion. -/
def ParallelNumericDependenciesEnabled
    (plan : CheckedParallelNumericPlan model)
    (table : CheckedParallelNumericAlternativeTable model)
    (state : ParallelNumericTransitionState) : Prop :=
  ∀ dependency ∈ plan.targetFields,
    table.referencesField dependency = true →
      dependency ∈ state.completedTargets

/-- One independently chosen successful whole-table batch. -/
inductive ParallelNumericRunTransition
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    ParallelNumericTransitionState → ParallelNumericRunBatch →
      ParallelNumericTransitionState → Prop where
  | compute
      (table : CheckedParallelNumericAlternativeTable model)
      (member : table ∈ plan.tables)
      (pending : table.targetField ∉ state.completedTargets)
      (enabled : ParallelNumericDependenciesEnabled plan table state)
      (outcomes : List ParallelNumericDirectOutcome)
      (executed :
        table.executeWithRead preliminary
          (plan.readPolicy state.runState preliminary.base) = .ok outcomes) :
      ParallelNumericRunTransition plan preliminary state
        (table.targetField, outcomes) {
          completedTargets := state.completedTargets ++ [table.targetField]
          outcomes := state.outcomes ++ outcomes
        }

/-- Finite successful closure used only for fixed-executor soundness. -/
inductive ParallelNumericRunTrace
    (plan : CheckedParallelNumericPlan model)
    (preliminary : CheckedIndexPreliminary model) :
    ParallelNumericTransitionState → List ParallelNumericRunBatch →
      ParallelNumericTransitionState → Prop where
  | nil (state) : ParallelNumericRunTrace plan preliminary state [] state
  | cons
      (step : ParallelNumericRunTransition plan preliminary state batch next)
      (rest : ParallelNumericRunTrace plan preliminary next batches final) :
      ParallelNumericRunTrace plan preliminary state (batch :: batches) final

end A12Kernel
