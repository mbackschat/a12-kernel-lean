import A12Kernel.Elaboration.NumericComputation.Run

/-! # Dependency-enabled checked Number-run relation

This capsule permits any pending scalar Number table whose statically referenced computed targets have completed under one caller-supplied `World`. It reuses the run's atomic evaluator and labels a successful step only with the target and rich outcome, so the relation can permit independent schedules beyond the fixed executor without introducing a generic scheduler or read trace. -/

namespace A12Kernel

abbrev NumericComputationRunLabel := FieldId × NumericTargetOutcome

namespace NumericComputationRunState

def targetFields (state : NumericComputationRunState) : List FieldId :=
  state.completed.map (·.targetField)

end NumericComputationRunState

/-- Static computed dependencies are complete. Runtime short-circuiting may still avoid reading one of them. -/
def NumericComputationDependenciesEnabled
    (run : CheckedNumericComputationRun model)
    (table : CheckedNumericComputationTable model)
    (state : NumericComputationRunState) : Prop :=
  ∀ dependency ∈ run.tables,
    table.referencesField dependency.targetField = true →
      dependency.targetField ∈ state.targetFields

inductive NumericComputationRunStep
    (run : CheckedNumericComputationRun model)
    (world : World)
    (input : CheckedDocument model) :
    NumericComputationRunState → NumericComputationRunLabel →
      NumericComputationRunState → Prop where
  | compute
      (table : CheckedNumericComputationTable model)
      (member : table ∈ run.tables)
      (pending : table.targetField ∉ state.targetFields)
      (enabled : NumericComputationDependenciesEnabled run table state)
      (completion : NumericComputationRunCompletion)
      (evaluated :
        run.evaluateTable world input state table = .ok completion) :
      NumericComputationRunStep run world input state
        (completion.targetField, completion.outcome)
        { completed := state.completed ++ [completion] }

inductive NumericComputationRunTrace
    (run : CheckedNumericComputationRun model)
    (world : World)
    (input : CheckedDocument model) :
    NumericComputationRunState → List NumericComputationRunLabel →
      NumericComputationRunState → Prop where
  | nil (state) : NumericComputationRunTrace run world input state [] state
  | cons
      (step : NumericComputationRunStep run world input state label next)
      (rest : NumericComputationRunTrace run world input next labels final) :
      NumericComputationRunTrace run world input state (label :: labels) final

end A12Kernel
