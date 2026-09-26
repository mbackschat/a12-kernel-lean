import A12Kernel.Elaboration.AddressedNumberBinary
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.ComputationRunPlan
import A12Kernel.Elaboration.NumericComputation.Table

/-! # Authored repeatable Number computation plans

An authored plan of Number steps at fixed and repeatable targets, put into dependency order by the
shared authored-order rule and executed one whole step at a time. A fixed step is a checked Number
table, whose aggregate reads rows through the plan. A row step is a direct copy or a two-source
addition, subtraction or multiplication computed at every row of its target's scope under an optional presence guard, each operand
addressed at its own scope, so an inner row reads an enclosing row's target at that row.

Every read goes through one overlay: a completed step's outcome at its exact address, a target of a
step not yet run as clean empty, and the immutable document otherwise. A stale stored value in a plan
target is therefore never read.

The two-level grid of the [checkpoint](../../docs/sources/evaluation-and-application-routes.md#src-two-level-repeatable-join)
calibrates one plan: a root aggregate over a guarded outer copy, and an inner join of an inner copy
with the enclosing outer target, the aggregate and the join authored ahead of what they read. Other
admitted shapes run by the same rules without a measurement of their own: the grid measures the direct
copy and addition, not subtraction or multiplication, and no row reads a poisoned guard.
-/

namespace A12Kernel

/-- The per-row Number operations a repeatable plan admits. -/
inductive CheckedRepeatableNumberRowOperation (model : FlatModel) where
  | direct (operation : CheckedAddressedNumberField model)
  | binary (operation : CheckedAddressedNumberBinary model)

namespace CheckedRepeatableNumberRowOperation

def target : CheckedRepeatableNumberRowOperation model → CheckedAddressedNumericTarget model
  | .direct operation => operation.placement.target
  | .binary operation => operation.pair.left.placement.target

def targetField (operation : CheckedRepeatableNumberRowOperation model) : FieldId :=
  operation.target.targetField

def sourceFields : CheckedRepeatableNumberRowOperation model → List FieldId
  | .direct operation => [operation.placement.sourceDeclaration.id]
  | .binary operation => [
      operation.pair.left.placement.sourceDeclaration.id,
      operation.pair.right.placement.sourceDeclaration.id]

def evaluateAtEnvironmentWithRead : CheckedRepeatableNumberRowOperation model →
    (CellAddr → Except CheckedDocumentError CheckedCell) → Env →
      Except AddressedNumericLeafFault NumericComputationResult
  | .direct operation, read, environment =>
      operation.toCheckedAddressedNumberSource.evaluateAtEnvironmentWithRead read environment
  | .binary operation, read, environment =>
      operation.evaluateAtEnvironmentWithRead read environment

end CheckedRepeatableNumberRowOperation

/-- One row operation under an optional presence guard. The guard reads only cells the target's row
binds and never the target itself, as a Number table's guard never reads its own target. -/
structure CheckedRepeatableNumberRowStep (model : FlatModel) where
  private mk ::
  operation : CheckedRepeatableNumberRowOperation model
  guard : Option ComputationCondition
  guardRowBound : guard.all
    (·.rowBoundBool model operation.target.targetDeclaration.repeatableScope) = true
  guardExcludesTarget : guard.all
    (fun condition => !condition.referencesField operation.targetField) = true

inductive RepeatableNumberRowStepError where
  | guardNotRowBound
  | guardReadsTarget (target : FieldId)
  deriving Repr, DecidableEq

def checkRepeatableNumberRowStep (operation : CheckedRepeatableNumberRowOperation model)
    (guard : Option ComputationCondition) :
    Except RepeatableNumberRowStepError (CheckedRepeatableNumberRowStep model) :=
  if hBound : guard.all
      (·.rowBoundBool model operation.target.targetDeclaration.repeatableScope) = true then
    if hTarget : guard.all
        (fun condition => !condition.referencesField operation.targetField) = true then
      .ok { operation, guard, guardRowBound := hBound, guardExcludesTarget := hTarget }
    else .error (.guardReadsTarget operation.targetField)
  else .error .guardNotRowBound

/-- One authored step of a repeatable Number plan. -/
inductive CheckedRepeatableNumberPlanStep (model : FlatModel) where
  /-- A Number table at a fixed target. -/
  | fixed (table : CheckedNumericComputationTable model)
  /-- A guarded row operation at a repeatable target. -/
  | row (step : CheckedRepeatableNumberRowStep model)

namespace CheckedRepeatableNumberPlanStep

def targetField : CheckedRepeatableNumberPlanStep model → FieldId
  | .fixed table => table.targetField
  | .row step => step.operation.targetField

/-- Whether the step's guard or operation reads one exact field, at any row. -/
def referencesField : CheckedRepeatableNumberPlanStep model → FieldId → Bool
  | .fixed table, field => table.referencesField field
  | .row step, field =>
      step.guard.any (·.referencesField field) || step.operation.sourceFields.contains field

end CheckedRepeatableNumberPlanStep

/-- Why an authored repeatable plan is refused. -/
inductive RepeatableNumberPlanError where
  | empty
  | duplicateTarget (target : FieldId)
  /-- `step` is a step ordering could not place and `reads` a pending target it reads. -/
  | cycle (step reads : FieldId)
  deriving Repr, DecidableEq

/-- An authored repeatable plan with its certified dependency order. -/
structure CheckedRepeatableNumberPlan (model : FlatModel) where
  private mk ::
  authored : List (CheckedRepeatableNumberPlanStep model)
  execution : List (CheckedRepeatableNumberPlanStep model)
  executionOrdered : execution = computationAuthoredOrder
    CheckedRepeatableNumberPlanStep.targetField CheckedRepeatableNumberPlanStep.referencesField
    authored.length authored
  uniqueTargets : FieldId.firstDuplicate? (authored.map (·.targetField)) = none
  dependenciesOrdered : firstForwardComputationDependency?
    CheckedRepeatableNumberPlanStep.targetField CheckedRepeatableNumberPlanStep.referencesField
    execution = none

/-- Certify an authored plan by ordering it. A forward read left after ordering can only wait on or
close a cycle. -/
def certifyRepeatableNumberPlan (steps : List (CheckedRepeatableNumberPlanStep model)) :
    Except RepeatableNumberPlanError (CheckedRepeatableNumberPlan model) :=
  if steps.isEmpty then .error .empty else
  match hDuplicate : FieldId.firstDuplicate? (steps.map (·.targetField)) with
  | some target => .error (.duplicateTarget target)
  | none =>
      match hForward : firstForwardComputationDependency?
          CheckedRepeatableNumberPlanStep.targetField
          CheckedRepeatableNumberPlanStep.referencesField
          (computationAuthoredOrder CheckedRepeatableNumberPlanStep.targetField
            CheckedRepeatableNumberPlanStep.referencesField steps.length steps) with
      | some (step, reads) => .error (.cycle step reads)
      | none => .ok {
          authored := steps
          execution := _
          executionOrdered := rfl
          uniqueTargets := hDuplicate
          dependenciesOrdered := hForward
        }

/-- A structural failure, with the target of the step that raised it. -/
inductive RepeatableNumberPlanFault where
  | row (target : FieldId) (cause : AddressedNumericLeafFault)
  | fixed (target : FieldId) (cause : NumericComputationFault)
  | fixedTargetCheck (target : FieldId) (cause : NumericTargetCheckFault)
  deriving Repr, DecidableEq

namespace CheckedRepeatableNumberPlan

def targetFields (plan : CheckedRepeatableNumberPlan model) : List FieldId :=
  plan.authored.map (·.targetField)

/-- Read one cell after the completed outcomes. A plan target no completion covers reads clean empty
rather than its stored value, as a pending target does in the scalar plan. -/
def read (plan : CheckedRepeatableNumberPlan model) (input : CheckedDocument model)
    (completed : List (SourcedNumericTargetOutcome CellAddr)) :
    CellAddr → Except CheckedDocumentError CheckedCell :=
  readAfterNumericDependenciesWith completed fun address =>
    if plan.targetFields.contains address.field then
      .ok (NumericDependencyCell.ofObservation .empty).checked
    else input.read address

private def cellAt (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell)
    (environment : Env) (field : FieldId) : CheckedCell :=
  match input.checkedCellWithRead read environment field with
  | .ok cell => cell
  | .error _ => malformedCheckedCell

private def executeRow (step : CheckedRepeatableNumberRowStep model)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except RepeatableNumberPlanFault (List (SourcedNumericTargetOutcome CellAddr)) :=
  step.operation.target.executeGuardedAtEnvironment input
    (fun environment => match step.guard with
      | none => .holds
      | some guard => guard.eval { read := cellAt input read environment })
    (step.operation.evaluateAtEnvironmentWithRead read)
  |>.mapError (.row step.operation.targetField)

private def executeFixed (table : CheckedNumericComputationTable model) (world : World)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except RepeatableNumberPlanFault (SourcedNumericTargetOutcome CellAddr) := do
  let checked ← table.evaluateIn {
      scalar := { read := cellAt input read [], world := some world }
      document := input.source.toDocument
      outer := []
      filterRead := cellAt input read
      starRead := cellAt input read
    } |>.mapError (.fixed table.targetField)
  let outcome ← match checked with
    | .supported outcome => pure outcome
    | .unsupported cause => throw (.fixedTargetCheck table.targetField cause)
  let target : CellAddr := { field := table.targetField, path := [] }
  pure { targetField := target, outcome, source := input.numericTargetPlacementStateAt target }

def executeSteps (plan : CheckedRepeatableNumberPlan model) (world : World)
    (input : CheckedDocument model) :
    List (CheckedRepeatableNumberPlanStep model) →
      List (SourcedNumericTargetOutcome CellAddr) →
      Except RepeatableNumberPlanFault (List (SourcedNumericTargetOutcome CellAddr))
  | [], completed => pure completed
  | step :: remaining, completed => do
      let read := plan.read input completed
      let outcomes ← match step with
        | .fixed table => (fun outcome => [outcome]) <$> executeFixed table world input read
        | .row row => executeRow row input read
      plan.executeSteps world input remaining (completed ++ outcomes)

/-- Run the certified order and return every outcome, grouped by step in that order and by row
within a step. -/
def execute (plan : CheckedRepeatableNumberPlan model) (world : World)
    (input : CheckedDocument model) :
    Except RepeatableNumberPlanFault (List (SourcedNumericTargetOutcome CellAddr)) :=
  plan.executeSteps world input plan.execution []

end CheckedRepeatableNumberPlan

end A12Kernel
