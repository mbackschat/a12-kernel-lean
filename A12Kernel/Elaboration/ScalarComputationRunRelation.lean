import A12Kernel.Elaboration.ScalarComputationRun

/-! # Dependency-enabled mixed scalar run relation

This relation permits any pending String or Number step whose statically referenced computed targets have completed. It reuses the mixed run's atomic evaluator and rich family-tagged outcome, so independent schedules can be analyzed without exposing a scheduler or public trace order.
-/

namespace A12Kernel

namespace ScalarComputationRunState

def targetFields (state : ScalarComputationRunState) : List FieldId :=
  state.completed.map (·.targetField)

end ScalarComputationRunState

/-- Every computed target structurally referenced by this step has completed. Runtime selection may still leave a reference unread. -/
def ScalarComputationDependenciesEnabled
    (run : CheckedScalarComputationRun model)
    (step : CheckedScalarComputationStep model)
    (state : ScalarComputationRunState) : Prop :=
  ∀ dependency ∈ run.targetFields,
    step.referencesField dependency = true →
      dependency ∈ state.targetFields

/-- One independently chosen successful mixed scalar transition. -/
inductive ScalarComputationRunTransition
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    ScalarComputationRunState → ScalarComputationOutcome →
      ScalarComputationRunState → Prop where
  | compute
      (step : CheckedScalarComputationStep model)
      (member : step ∈ run.steps)
      (pending : step.targetField ∉ state.targetFields)
      (enabled : ScalarComputationDependenciesEnabled run step state)
      (completion : ScalarComputationCompletion)
      (evaluated :
        run.evaluateStep world patterns input state step = .ok completion) :
      ScalarComputationRunTransition run world patterns input state
        completion.outcome
        { completed := state.completed ++ [completion] }

/-- One independently chosen enabled mixed scalar step whose structural evaluation fault terminates execution without advancing completed state. Rich rejected or cleared target outcomes remain successful transitions rather than failures here. -/
inductive ScalarComputationRunFailureTransition
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    ScalarComputationRunState → ScalarComputationRunFault → Prop where
  | fail
      (step : CheckedScalarComputationStep model)
      (member : step ∈ run.steps)
      (pending : step.targetField ∉ state.targetFields)
      (enabled : ScalarComputationDependenciesEnabled run step state)
      (evaluated :
        run.evaluateStep world patterns input state step = .error fault) :
      ScalarComputationRunFailureTransition run world patterns input state fault

/-- Finite closure used to relate successful fixed execution to independent transitions. -/
inductive ScalarComputationRunTrace
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    ScalarComputationRunState → List ScalarComputationOutcome →
      ScalarComputationRunState → Prop where
  | nil (state) : ScalarComputationRunTrace run world patterns input state [] state
  | cons
      (step : ScalarComputationRunTransition run world patterns input
        state outcome next)
      (rest : ScalarComputationRunTrace run world patterns input
        next outcomes final) :
      ScalarComputationRunTrace run world patterns input state
        (outcome :: outcomes) final

/-- A finite successful prefix followed by one enabled structural failure at the unchanged terminal state. -/
inductive ScalarComputationRunFailureTrace
    (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    ScalarComputationRunState → List ScalarComputationOutcome →
      ScalarComputationRunState → ScalarComputationRunFault → Prop where
  | failed
      (failure : ScalarComputationRunFailureTransition run world patterns input
        state fault) :
      ScalarComputationRunFailureTrace run world patterns input
        state [] state fault
  | cons
      (step : ScalarComputationRunTransition run world patterns input
        state outcome next)
      (rest : ScalarComputationRunFailureTrace run world patterns input
        next outcomes final fault) :
      ScalarComputationRunFailureTrace run world patterns input
        state (outcome :: outcomes) final fault

end A12Kernel
