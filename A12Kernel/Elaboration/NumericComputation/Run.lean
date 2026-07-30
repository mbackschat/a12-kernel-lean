import A12Kernel.Elaboration.CheckedDocument
import A12Kernel.Elaboration.NumericComputation.RunPlan
import A12Kernel.Semantics.NumericDependency

/-! # Checked nonrepeatable Number computation runs

This capsule executes a finite scalar Number plan in its certified supplied order under one caller-supplied evaluation `World`. Pending computed targets hide stored document content, completed targets expose their typed dependency cells, and every ordinary input delegates to the immutable checked document. The run retains rich target outcomes only; result projection, application, messages, validation, repeatable activation, and heterogeneous scheduling remain separate.
-/

namespace A12Kernel

/-- One completed Number target. The dependency cell remains a deterministic projection of the retained rich outcome. -/
structure NumericComputationRunCompletion where
  targetField : FieldId
  outcome : NumericTargetOutcome
  deriving Repr, DecidableEq

structure NumericComputationRunState where
  completed : List NumericComputationRunCompletion := []
  deriving Repr, DecidableEq

namespace NumericComputationRunState

def find? (state : NumericComputationRunState) (field : FieldId) :
    Option NumericComputationRunCompletion :=
  state.completed.find? fun completion => completion.targetField == field

def outcomes (state : NumericComputationRunState) :
    List (FieldId × NumericTargetOutcome) :=
  state.completed.map fun completion =>
    (completion.targetField, completion.outcome)

end NumericComputationRunState

/-- Structural failures from an already-checked scalar Number run. An unsupported target result remains outside semantic no-value and poison. -/
inductive NumericComputationRunFault where
  | evaluation (target : FieldId) (fault : NumericComputationFault)
  | targetCheck (target : FieldId) (fault : NumericTargetCheckFault)
  deriving Repr, DecidableEq

namespace CheckedNumericComputationTable

/-- Evaluate one checked scalar Number table against an explicit context and retain its complete target outcome. Homogeneous and heterogeneous runs share this atomic boundary. -/
def evaluateCompletion (table : CheckedNumericComputationTable model)
    (context : ScalarComputationContext) :
    Except NumericComputationRunFault NumericComputationRunCompletion :=
  match table.evaluate context with
  | .error fault => .error (.evaluation table.targetField fault)
  | .ok (.unsupported fault) =>
      .error (.targetCheck table.targetField fault)
  | .ok (.supported outcome) =>
      .ok { targetField := table.targetField, outcome }

end CheckedNumericComputationTable

namespace CheckedNumericComputationRun

def targetFields (run : CheckedNumericComputationRun model) :
    List FieldId :=
  run.tables.map (·.targetField)

/-- Hide pending computed targets, expose completed Number outcomes, and delegate every non-target read to the checked document. -/
def readPolicy (run : CheckedNumericComputationRun model)
    (state : NumericComputationRunState) (input : CheckedDocument model) :
    ScalarComputationContext where
  read field :=
    if run.targetFields.contains field then
      match state.find? field with
      | some completion =>
          (NumericDependencyCell.ofOutcome completion.outcome).checked
      | none =>
          (NumericDependencyCell.ofObservation .empty).checked
    else
      input.flatContext.read field

/-- Evaluate one checked table through the current overlay and retain its complete target outcome. -/
def evaluateTable (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model)
    (state : NumericComputationRunState)
    (table : CheckedNumericComputationTable model) :
    Except NumericComputationRunFault NumericComputationRunCompletion :=
  table.evaluateCompletion ((run.readPolicy state input).withWorld world)

/-- Execute one supplied-order table suffix through the same immutable input and transient overlay. -/
def executeTables (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model) :
    List (CheckedNumericComputationTable model) →
      NumericComputationRunState →
      Except NumericComputationRunFault NumericComputationRunState
  | [], state => pure state
  | table :: remaining, state =>
      match run.evaluateTable world input state table with
      | .error fault => .error fault
      | .ok completion =>
          executeTables run world input remaining {
            completed := state.completed ++ [completion]
          }

/-- Execute the certified fixed order under one unchanged world and return rich target outcomes in that same order. -/
def execute (run : CheckedNumericComputationRun model)
    (world : World) (input : CheckedDocument model) :
    Except NumericComputationRunFault
      (List (FieldId × NumericTargetOutcome)) :=
  match run.executeTables world input run.tables {} with
  | .error fault => .error fault
  | .ok state => .ok state.outcomes

end CheckedNumericComputationRun

end A12Kernel
