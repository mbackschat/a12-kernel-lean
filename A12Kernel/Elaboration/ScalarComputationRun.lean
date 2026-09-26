import A12Kernel.Elaboration.NumericComputation.Run
import A12Kernel.Elaboration.StringComputationRun
import A12Kernel.Semantics.HeterogeneousComputationDependency

/-! # Finite checked mixed scalar computation runs

This capsule composes already-consolidated checked String and scalar Number tables in one supplied order. Every step, completion, fault, and outcome retains its family. Pending targets hide source state; completed targets are projected only when a consumer context reads them, so a Number remains numeric for Number computation and becomes canonical text for String computation.

An authored plan of any length is put into dependency order first, by running the earliest authored step that reads no other pending target; the plan's own order is not a supplied one. Same-target grouping remains in each family owner. Family result projection, whole-document application, repeatable targets, and a generic dependency graph remain separate.
-/

namespace A12Kernel

/-- One already-consolidated checked scalar computation table with its target family retained. -/
inductive CheckedScalarComputationStep (model : FlatModel) where
  | string (table : CheckedStringComputationTable model)
  | number (table : CheckedNumericComputationTable model)

/-- One checked mixed scalar step projected for pre-schedule analysis without requiring or choosing a run order. -/
structure ScalarComputationStepDependency where
  targetField : FieldId
  targetKind : SurfaceScalarKind
  fieldDependencies : List FieldId
  deriving Repr, DecidableEq

namespace CheckedScalarComputationStep

def targetField : CheckedScalarComputationStep model → FieldId
  | .string table => table.targetField
  | .number table => table.targetField

def targetKind : CheckedScalarComputationStep model → SurfaceScalarKind
  | .string _ => .string
  | .number _ => .number

def referencesField (step : CheckedScalarComputationStep model)
    (field : FieldId) : Bool :=
  match step with
  | .string table => table.referencesField field
  | .number table => table.referencesField field

/-- Enumerate every model field referenced by this checked typed step. The model order is stable while the predicate traverses the step's complete guards and operations. -/
def fieldDependencies (step : CheckedScalarComputationStep model) :
    List FieldId :=
  (model.fields.filter fun declaration =>
    step.referencesField declaration.id).map (·.id)

/-- Retain one checked step's family and complete raw dependency set before any run-order certificate exists. -/
def dependencyAnalysis (step : CheckedScalarComputationStep model) :
    ScalarComputationStepDependency := {
  targetField := step.targetField
  targetKind := step.targetKind
  fieldDependencies := step.fieldDependencies
}

def supportsScalarEvaluation : CheckedScalarComputationStep model → Bool
  | .string _ => true
  | .number table => table.supportsScalarEvaluation

end CheckedScalarComputationStep

/-- Project a finite candidate step list for analysis without constructing a graph or accepting a schedule. -/
def analyzeScalarComputationSteps
    (steps : List (CheckedScalarComputationStep model)) :
    List ScalarComputationStepDependency :=
  steps.map (·.dependencyAnalysis)

def firstNonScalarComputationStep? :
    List (CheckedScalarComputationStep model) → Option FieldId
  | [] => none
  | step :: remaining =>
      if step.supportsScalarEvaluation then
        firstNonScalarComputationStep? remaining
      else
        some step.targetField

def firstForwardScalarComputationDependency?
    (steps : List (CheckedScalarComputationStep model)) :
    Option (FieldId × FieldId) :=
  firstForwardComputationDependency?
    CheckedScalarComputationStep.targetField
    CheckedScalarComputationStep.referencesField steps

inductive ScalarComputationRunPlanError where
  | empty
  | repeatableContextRequired (target : FieldId)
  | duplicateTarget (target : FieldId)
  | forwardDependency (consumer dependency : FieldId)
  deriving Repr, DecidableEq

/-- A finite mixed scalar run over preconsolidated family tables, with unique targets and backward-only dependencies. -/
structure CheckedScalarComputationRun (model : FlatModel) where
  steps : List (CheckedScalarComputationStep model)
  nonempty : steps ≠ []
  scalarSteps : firstNonScalarComputationStep? steps = none
  uniqueTargets :
    FieldId.firstDuplicate? (steps.map (·.targetField)) = none
  dependenciesOrdered :
    firstForwardScalarComputationDependency? steps = none

/-- Certify a mixed scalar run while retaining the exact supplied steps for callers that add a stronger wrapper invariant. -/
private def certifyScalarComputationRunWithSteps
    (steps : List (CheckedScalarComputationStep model)) :
    Except ScalarComputationRunPlanError
      { run : CheckedScalarComputationRun model // run.steps = steps } :=
  match steps with
  | [] => .error .empty
  | first :: remaining =>
      match hScalar :
          firstNonScalarComputationStep? (first :: remaining) with
      | some target => .error (.repeatableContextRequired target)
      | none =>
          match hDuplicate :
              FieldId.firstDuplicate?
                ((first :: remaining).map (·.targetField)) with
          | some target => .error (.duplicateTarget target)
          | none =>
              match hForward :
                  firstForwardScalarComputationDependency?
                    (first :: remaining) with
              | some (consumer, dependency) =>
                  .error (.forwardDependency consumer dependency)
              | none => .ok {
                  val := {
                    steps := first :: remaining
                    nonempty := by simp
                    scalarSteps := hScalar
                    uniqueTargets := hDuplicate
                    dependenciesOrdered := hForward
                  }
                  property := rfl
                }

/-- Certify only cross-table scalar scheduling obligations. Family owners remain responsible for same-target assembly and checked table legality. -/
def certifyScalarComputationRun
    (steps : List (CheckedScalarComputationStep model)) :
    Except ScalarComputationRunPlanError
      (CheckedScalarComputationRun model) :=
  match certifyScalarComputationRunWithSteps steps with
  | .error cause => .error cause
  | .ok run => .ok run.1

/-- The first step of `scan` that reads no target of another step in `pending`, and `scan`
without it. A step's own target does not block it: a self-read is the family owner's refusal. -/
def firstReadyScalarComputationStep?
    (pending : List (CheckedScalarComputationStep model)) :
    List (CheckedScalarComputationStep model) →
      Option (CheckedScalarComputationStep model × List (CheckedScalarComputationStep model))
  | [] => none
  | step :: rest =>
      if pending.all fun other =>
          other.targetField == step.targetField || !step.referencesField other.targetField then
        some (step, rest)
      else
        (firstReadyScalarComputationStep? pending rest).map fun (ready, remaining) =>
          (ready, step :: remaining)

/-- Run the earliest authored step that reads no other pending target, then repeat. When every
pending step reads another pending target, the steps left form or wait on a cycle and stay in
authored order, where run certification reports the first forward read among them. -/
def scalarComputationAuthoredOrder :
    Nat → List (CheckedScalarComputationStep model) → List (CheckedScalarComputationStep model)
  | 0, pending => pending
  | fuel + 1, pending =>
      match firstReadyScalarComputationStep? pending pending with
      | none => pending
      | some (ready, remaining) => ready :: scalarComputationAuthoredOrder fuel remaining

/-- The dependency order of an authored plan. Among the orders that run every producer before its
readers, it keeps each independent step at its earliest authored place; which of those orders the
Kernel takes is not observable, since independent steps read nothing of each other. -/
def scalarComputationAuthoredExecutionSteps
    (steps : List (CheckedScalarComputationStep model)) :
    List (CheckedScalarComputationStep model) :=
  scalarComputationAuthoredOrder steps.length steps

/-- An authored plan of scalar steps with its certified dependency order. The authored order stays
available to analysis consumers while execution reuses the finite checked run. -/
structure CheckedScalarComputationPlan (model : FlatModel) where
  private mk ::
  authored : List (CheckedScalarComputationStep model)
  execution : CheckedScalarComputationRun model
  executionUsesSelectedSteps :
    execution.steps = scalarComputationAuthoredExecutionSteps authored

/-- Certify an authored plan by ordering it and certifying that order as a run. A cycle leaves a
forward read in the order and is refused with it. -/
def certifyScalarComputationPlan
    (steps : List (CheckedScalarComputationStep model)) :
    Except ScalarComputationRunPlanError (CheckedScalarComputationPlan model) :=
  match certifyScalarComputationRunWithSteps
      (scalarComputationAuthoredExecutionSteps steps) with
  | .error cause => .error cause
  | .ok execution => .ok {
      authored := steps
      execution := execution.1
      executionUsesSelectedSteps := execution.2
    }

namespace CheckedScalarComputationPlan

/-- Target identities in caller-authored order for Analyze consumers. -/
def authoredTargetFields (plan : CheckedScalarComputationPlan model) : List FieldId :=
  plan.authored.map (·.targetField)

/-- Target identities in the certified checked execution order. -/
def executionTargetFields (plan : CheckedScalarComputationPlan model) : List FieldId :=
  plan.execution.steps.map (·.targetField)

end CheckedScalarComputationPlan

/-- One completed rich target outcome with its family and target identity retained. -/
inductive ScalarComputationOutcome where
  | string (target : FieldId) (outcome : StringTargetOutcome)
  | number (target : FieldId) (outcome : NumericTargetOutcome)
  deriving Repr, DecidableEq

/-- Internal typed completion used to defer consumer-specific dependency projection until a read is reached. -/
inductive ScalarComputationCompletion where
  | string (completion : StringComputationRunCompletion)
  | number (completion : NumericComputationRunCompletion)

namespace ScalarComputationCompletion

def targetField : ScalarComputationCompletion → FieldId
  | .string completion => completion.targetField
  | .number completion => completion.targetField

def outcome : ScalarComputationCompletion → ScalarComputationOutcome
  | .string completion =>
      .string completion.targetField completion.outcome
  | .number completion =>
      .number completion.targetField completion.outcome

/-- Project a completed target only for a reached String-family read. -/
def stringCell : ScalarComputationCompletion → CheckedCell
  | .string completion => completion.dependencyCell.checked
  | .number completion =>
      (StringDependencyCell.ofNumericOutcome completion.outcome).checked

/-- Project a completed target only for a reached Number-family read. -/
def numberCell : ScalarComputationCompletion → CheckedCell
  | .string completion => completion.dependencyCell.checked
  | .number completion =>
      (NumericDependencyCell.ofOutcome completion.outcome).checked

end ScalarComputationCompletion

structure ScalarComputationRunState where
  completed : List ScalarComputationCompletion := []

namespace ScalarComputationRunState

def find? (state : ScalarComputationRunState) (field : FieldId) :
    Option ScalarComputationCompletion :=
  state.completed.find? fun completion => completion.targetField == field

def outcomes (state : ScalarComputationRunState) :
    List ScalarComputationOutcome :=
  state.completed.map (·.outcome)

end ScalarComputationRunState

inductive ScalarComputationRunFault where
  | string (cause : StringComputationRunFault)
  | number (cause : NumericComputationRunFault)
  deriving Repr, DecidableEq

namespace ScalarComputationRunFault

/-- Project the target retained by the fault's original computation family. -/
def target : ScalarComputationRunFault → FieldId
  | .string cause => cause.target
  | .number cause => cause.target

def targetKind : ScalarComputationRunFault → SurfaceScalarKind
  | .string _ => .string
  | .number _ => .number

end ScalarComputationRunFault

namespace CheckedScalarComputationRun

def targetFields (run : CheckedScalarComputationRun model) :
    List FieldId :=
  run.steps.map (·.targetField)

/-- Project completed targets for String consumption, hide suffix-owned pending targets, and delegate ordinary reads to the String document context. A completion may belong to an earlier checked phase rather than to this run. -/
def stringContext (run : CheckedScalarComputationRun model)
    (state : ScalarComputationRunState)
    (input : CheckedDocument model) : StringComputationContext where
  read field :=
    match state.find? field with
    | some completion => completion.stringCell
    | none =>
        if run.targetFields.contains field then
          StringDependencyCell.empty.checked
        else
          input.stringComputationContext.read field

/-- Project completed targets for Number consumption, hide suffix-owned pending targets, and delegate ordinary reads to the scalar document context under one unchanged world. A completion may belong to an earlier checked phase rather than to this run. -/
def numberContext (run : CheckedScalarComputationRun model)
    (world : World) (state : ScalarComputationRunState)
    (input : CheckedDocument model) : ScalarComputationContext :=
  let source := input.scalarComputationContext world
  { source with
    read := fun field =>
      match state.find? field with
      | some completion => completion.numberCell
      | none =>
          if run.targetFields.contains field then
            (NumericDependencyCell.ofObservation .empty).checked
          else
            source.read field
  }

/-- Evaluate one family-tagged table through its matching consumer context and retain its typed completion. -/
def evaluateStep (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model)
    (state : ScalarComputationRunState) :
    CheckedScalarComputationStep model →
      Except ScalarComputationRunFault ScalarComputationCompletion
  | .string table =>
      match table.evaluateCompletion patterns
          (run.stringContext state input) with
      | .ok completion => .ok (.string completion)
      | .error cause => .error (.string cause)
  | .number table =>
      match table.evaluateCompletion
          (run.numberContext world state input) with
      | .ok completion => .ok (.number completion)
      | .error cause => .error (.number cause)

def executeSteps (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    List (CheckedScalarComputationStep model) →
      ScalarComputationRunState →
      Except ScalarComputationRunFault ScalarComputationRunState
  | [], state => pure state
  | step :: remaining, state => do
      let completion ← run.evaluateStep world patterns input state step
      executeSteps run world patterns input remaining {
        completed := state.completed ++ [completion]
      }

/-- Execute the certified mixed order and return rich family-tagged outcomes in that same order. -/
def execute (run : CheckedScalarComputationRun model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except ScalarComputationRunFault (List ScalarComputationOutcome) := do
  let state ← run.executeSteps world patterns input run.steps {}
  pure state.outcomes

end CheckedScalarComputationRun

namespace CheckedScalarComputationPlan

/-- Execute the dependency-ordered plan through the existing typed mixed-run evaluator. -/
def execute (plan : CheckedScalarComputationPlan model)
    (world : World)
    (patterns : PreparedFlatStringPatterns model compilePattern)
    (input : CheckedDocument model) :
    Except ScalarComputationRunFault (List ScalarComputationOutcome) :=
  plan.execution.execute world patterns input

end CheckedScalarComputationPlan

end A12Kernel
