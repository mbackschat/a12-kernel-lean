import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.StringComputationRunPlan
import A12Kernel.Semantics.StringCascade

/-! # Checked nonrepeatable String computation runs

This capsule executes a finite, statically ordered list of checked String tables. Plan certification rejects duplicate targets and any computed-field read whose producer has not already run. During execution, every run target is stripped from the immutable checked document: a pending target reads as empty and a completed target reads through the dependency observation derived from its rich outcome.

The transient overlay is the only new state. Result projection, application, messages, validation, alternative ordering, and target checking remain with their existing owners or later capsules.
-/

namespace A12Kernel

/-- One completed target with the exact dependency observation later reads must receive. Caching this checked cell keeps run reads pure and preserves conversion failure as a structural fault. -/
structure StringComputationRunCompletion where
  targetField : FieldId
  outcome : StringTargetOutcome
  dependencyCell : StringDependencyCell

/-- The ordered insert-once overlay accumulated while the checked plan executes. -/
structure StringComputationRunState where
  completed : List StringComputationRunCompletion := []

namespace StringComputationRunState

def find? (state : StringComputationRunState) (field : FieldId) :
    Option StringComputationRunCompletion :=
  state.completed.find? fun completion => completion.targetField == field

def outcomes (state : StringComputationRunState) :
    List (FieldId × StringTargetOutcome) :=
  state.completed.map fun completion => (completion.targetField, completion.outcome)

end StringComputationRunState

inductive StringComputationRunFault where
  | evaluation (target : FieldId) (fault : StringComputationFault)
  | dependency (target : FieldId) (fault : StringDependencyFault)
  deriving Repr, DecidableEq

namespace CheckedStringComputationRun

def targetFields (run : CheckedStringComputationRun model) : List FieldId :=
  run.tables.map (·.targetField)

/-- Read ordinary inputs from the checked document, hide every pending computed target, and expose only completed semantic outcomes at computed targets. -/
def readPolicy (run : CheckedStringComputationRun model)
    (state : StringComputationRunState) (input : CheckedDocument model) :
    StringComputationContext where
  read field :=
    if run.targetFields.contains field then
      match state.find? field with
      | some completion => completion.dependencyCell.checked
      | none => StringDependencyCell.empty.checked
    else
      input.flatContext.read field

/-- Execute an explicitly supplied suffix with the same checked run read policy. The public suffix form is the induction boundary for the run relation; `execute` is its only whole-plan entry point. -/
def executeTables (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    List (CheckedStringComputationTable model) → StringComputationRunState →
      Except StringComputationRunFault StringComputationRunState
  | [], state => pure state
  | table :: remaining, state =>
      match patterns.targetMatcher? table.targetField with
      | none =>
          .error (.evaluation table.targetField
            (.targetPatternUnavailable table.targetField))
      | some matcher =>
          match table.evaluateOutcomeWithPattern matcher
              (run.readPolicy state input) with
          | .error fault => .error (.evaluation table.targetField fault)
          | .ok outcome =>
              match StringDependencyCell.ofOutcome outcome with
              | .error fault => .error (.dependency table.targetField fault)
              | .ok dependencyCell =>
                  executeTables run patterns input remaining {
                    completed := state.completed ++ [{
                      targetField := table.targetField
                      outcome
                      dependencyCell
                    }]
                  }

/-- Execute the certified fixed order against one immutable checked document and return rich outcomes in that same order. Pattern preparation is supplied separately because the checked document intentionally retains only checked cells. -/
def execute (run : CheckedStringComputationRun model)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except StringComputationRunFault (List (FieldId × StringTargetOutcome)) := do
  pure (← executeTables run patterns input run.tables {}).outcomes

end CheckedStringComputationRun

end A12Kernel
