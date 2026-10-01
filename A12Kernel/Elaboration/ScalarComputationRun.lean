import A12Kernel.Elaboration.ComputationNormalForm
import A12Kernel.Elaboration.DocumentComputationStep
import A12Kernel.Elaboration.NumericComputation.Run
import A12Kernel.Elaboration.StringComputationRun
import A12Kernel.Semantics.HeterogeneousComputationDependency

/-! # Finite checked mixed scalar computation runs

This capsule composes already-consolidated checked String and scalar Number tables and whole-document steps (`CheckedDocumentComputationStep`). A run executes them in one supplied order. Every step, completion, fault, and outcome retains its family. Pending targets hide source state; completed targets are projected only when a consumer reads them, so a Number remains numeric for Number computation and becomes canonical text for String computation, and a whole-document target is read as its step's read-back cell. A whole-document step runs against the document overlaid with those projections.

An authored plan of any length over the same flat scalar steps is put into dependency order first, by running the earliest authored step that reads no other pending target, and a plan some of whose steps are read-closed is refused as a cycle. Same-target grouping remains in each family owner. Family result projection, whole-document application, and repeatable targets remain separate.
-/

namespace A12Kernel

/-- One already-consolidated checked scalar computation table with its target family retained. -/
inductive CheckedScalarComputationStep (model : FlatModel) where
  | string (table : CheckedStringComputationTable model)
  | number (table : CheckedNumericComputationTable model)
  | document (step : CheckedDocumentComputationStep model)

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
  | .document step => step.target

def targetKind : CheckedScalarComputationStep model → SurfaceScalarKind
  | .string _ => .string
  | .number _ => .number
  | .document step => step.targetKind

def referencesField (step : CheckedScalarComputationStep model)
    (field : FieldId) : Bool :=
  match step with
  | .string table => table.referencesField field
  | .number table => table.referencesField field
  | .document step => step.referencesField field

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
  | .string _ | .document _ => true
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
def certifyScalarComputationRunWithSteps
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

/-- The dependency order of an authored plan, by the shared authored-order rule. -/
def scalarComputationAuthoredExecutionSteps
    (steps : List (CheckedScalarComputationStep model)) :
    List (CheckedScalarComputationStep model) :=
  computationAuthoredOrder CheckedScalarComputationStep.targetField
    CheckedScalarComputationStep.referencesField steps.length steps

/-- Why an authored plan is refused. It shares the run's structural gates, but a plan has no order
error: after ordering, a step still reads a later target only where some of its steps are
read-closed. -/
inductive ScalarComputationPlanError where
  | empty
  | repeatableContextRequired (target : FieldId)
  | duplicateTarget (target : FieldId)
  /-- `step` is a step ordering could not place and `reads` a pending target it reads. `step` may
  wait on the cycle rather than close it; which members the Kernel spells out is not projected. -/
  | cycle (step reads : FieldId)
  deriving Repr, DecidableEq

/-- An authored plan of scalar steps with its certified dependency order. The authored order stays
available to analysis consumers while execution reuses the finite checked run. -/
structure CheckedScalarComputationPlan (model : FlatModel) where
  private mk ::
  authored : List (CheckedScalarComputationStep model)
  execution : CheckedScalarComputationRun model
  executionUsesSelectedSteps :
    execution.steps = scalarComputationAuthoredExecutionSteps authored

/-- Certify an authored plan by ordering it and certifying that order as a run. -/
def certifyScalarComputationPlan
    (steps : List (CheckedScalarComputationStep model)) :
    Except ScalarComputationPlanError (CheckedScalarComputationPlan model) :=
  -- The run refusal is translated here and nowhere else, so a supplied-order run's forward read
  -- has no route to the cycle refusal.
  match certifyScalarComputationRunWithSteps
      (scalarComputationAuthoredExecutionSteps steps) with
  | .error .empty => .error .empty
  | .error (.repeatableContextRequired target) => .error (.repeatableContextRequired target)
  | .error (.duplicateTarget target) => .error (.duplicateTarget target)
  | .error (.forwardDependency step reads) => .error (.cycle step reads)
  | .ok execution => .ok {
      authored := steps
      execution := execution.1
      executionUsesSelectedSteps := execution.2
    }

/-- The Kernel class a plan refusal draws. The Kernel sorts the computed fields before it
generates anything and refuses a cycle among them as `MVK_ERROR_CALC_CYCLE`
([`spec/09`](../../spec/09-computations.md) §1). The same clause lists classes measured beside a
cycle that withhold it, among them another computation's text defect or member class, a rule's text
defect, a structural path class, and a missing error text, so the class holds only for a model free
of them. A plan sees none of them, and a variant-filtered declaration is not one of its steps. The
structural gates claim no class. -/
def ScalarComputationPlanError.calculationRefusal? :
    ScalarComputationPlanError → Option CalculationRefusal
  | .cycle _ _ => some .calcCycle
  | .empty | .repeatableContextRequired _ | .duplicateTarget _ => none

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
  | document (target : FieldId) (outcome : DocumentTargetOutcome)
  deriving Repr, DecidableEq

/-- Internal typed completion used to defer consumer-specific dependency projection until a read is reached. A whole-document completion carries the one cell every consumer reads. -/
inductive ScalarComputationCompletion where
  | string (completion : StringComputationRunCompletion)
  | number (completion : NumericComputationRunCompletion)
  | document (target : FieldId) (outcome : DocumentTargetOutcome) (cell : CheckedCell)

namespace ScalarComputationCompletion

def targetField : ScalarComputationCompletion → FieldId
  | .string completion => completion.targetField
  | .number completion => completion.targetField
  | .document target _ _ => target

def outcome : ScalarComputationCompletion → ScalarComputationOutcome
  | .string completion =>
      .string completion.targetField completion.outcome
  | .number completion =>
      .number completion.targetField completion.outcome
  | .document target outcome _ => .document target outcome

/-- Project a completed target only for a reached String-family read. -/
def stringCell : ScalarComputationCompletion → CheckedCell
  | .string completion => completion.dependencyCell.checked
  | .number completion =>
      (StringDependencyCell.ofNumericOutcome completion.outcome).checked
  | .document _ _ cell => cell

/-- Project a completed target for a reached Number-family read, which is also the read every
whole-document evaluator makes. -/
def numberCell : ScalarComputationCompletion → CheckedCell
  | .string completion => completion.dependencyCell.checked
  | .number completion =>
      (NumericDependencyCell.ofOutcome completion.outcome).checked
  | .document _ _ cell => cell

/-- The Number formal-read text a completed target places in the document a whole-document step reads:
the same rendering the String-family read gives it, so the two reads cannot disagree. -/
def numberFormalReadText? : ScalarComputationCompletion → Option String
  | .number completion =>
      match completion.outcome with
      | .accepted stored => some stored.render
      | _ => none
  | .string _ | .document _ _ _ => none

/-- The placement a completed target takes in the document a whole-document step reads. -/
def placement (completion : ScalarComputationCompletion) : CheckedCellPlacement where
  address := { field := completion.targetField, path := [] }
  cell := completion.numberCell
  numericFormalReadText := completion.numberFormalReadText?

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
  | document (target : FieldId) (kind : SurfaceScalarKind) (cause : DocumentComputationStepFault)
  deriving Repr, DecidableEq

namespace ScalarComputationRunFault

/-- Project the target retained by the fault's original computation family. -/
def target : ScalarComputationRunFault → FieldId
  | .string cause => cause.target
  | .number cause => cause.target
  | .document target _ _ => target

def targetKind : ScalarComputationRunFault → SurfaceScalarKind
  | .string _ => .string
  | .number _ => .number
  | .document _ kind _ => kind

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

/-- The whole document a whole-document step reads: each completed target through its Number-family
cell and formal-read text, each pending one empty. -/
def documentFor (run : CheckedScalarComputationRun model)
    (state : ScalarComputationRunState) (input : CheckedDocument model) : CheckedDocument model :=
  input.overlayNonrepeatableCells
    (state.completed.map (fun completion => (completion.targetField, some completion.placement)) ++
      (run.targetFields.filter fun field => (state.find? field).isNone).map (·, none))

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
  | .document step =>
      match step.run world (run.documentFor state input) with
      | .ok (outcome, cell) => .ok (.document step.target outcome cell)
      | .error cause => .error (.document step.target step.targetKind cause)

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
