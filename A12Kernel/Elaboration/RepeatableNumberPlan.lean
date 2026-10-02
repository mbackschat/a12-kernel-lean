import A12Kernel.Elaboration.AddressedNumberField
import A12Kernel.Elaboration.CheckedStarDocument
import A12Kernel.Elaboration.ComputationRunPlan
import A12Kernel.Elaboration.NumericComputation.RunPlan

/-! # Authored repeatable Number computation plans

An authored plan of Number tables at fixed and repeatable targets, put into dependency order by the
shared authored-order rule and executed one whole table at a time. At a fixed target a table's
aggregate reads rows through the plan. At a repeatable target the table runs at every row of the
target's scope, selecting among its guarded alternatives as a fixed table selects, through a context
reading each operand at its own scope under that row, as an ordinary operand is read
([`spec/09`](../../spec/09-computations.md) §5): an inner row reads an enclosing row's target at that
row. Such a table admits only operations the scalar evaluator runs, so no aggregate reads rows from
inside a row.

Every read goes through one overlay: a completed step's outcome at its exact address, a target of a
step not yet run as clean empty, and the immutable document otherwise. A stale stored value in a plan
target is therefore never read.

The two-level grid of the [checkpoint](../../docs/sources/computation-scheduling-probes.md#src-two-level-repeatable-join)
calibrates one plan: a root aggregate over a guarded outer copy, and an inner join of an inner copy
with the enclosing outer target, the aggregate and the join authored ahead of what they read. The
[operator checkpoint](../../docs/sources/computation-scheduling-probes.md#src-repeatable-join-operators-and-guards),
the [guard-source checkpoint](../../docs/sources/computation-scheduling-probes.md#src-guard-on-malformed-source)
and the row-producer grid its conformance module cites measure subtraction, multiplication, fill
guards on computed and malformed sources, and the extrema, rounded division, `Abs`, `FirstFilledValue`
and value count at a row.
-/

namespace A12Kernel

/-- Why an authored repeatable plan is refused. -/
inductive RepeatableNumberPlanError where
  | empty
  | duplicateTarget (target : FieldId)
  /-- A table at a repeatable target holds an operation the scalar evaluator cannot run, such as an
  aggregate over a star, whose read from inside a row no measurement covers. -/
  | rowTableNotScalar (target : FieldId)
  /-- `step` is a step ordering could not place and `reads` a pending target it reads. -/
  | cycle (step reads : FieldId)
  deriving Repr, DecidableEq

/-- An authored repeatable plan with its certified dependency order. -/
structure CheckedRepeatableNumberPlan (model : FlatModel) where
  private mk ::
  authored : List (CheckedNumericComputationTable model)
  execution : List (CheckedNumericComputationTable model)
  executionOrdered : execution = computationAuthoredOrder
    CheckedNumericComputationTable.targetField CheckedNumericComputationTable.referencesField
    authored.length authored
  uniqueTargets : FieldId.firstDuplicate? (authored.map (·.targetField)) = none
  dependenciesOrdered : firstForwardComputationDependency?
    CheckedNumericComputationTable.targetField CheckedNumericComputationTable.referencesField
    execution = none

/-- The target of a table at a repeatable target holding an operation the scalar evaluator cannot run. -/
private def rowTableNotScalar? (table : CheckedNumericComputationTable model) : Option FieldId :=
  if !table.readingScope.isEmpty && !table.atomsSupportScalarEvaluation then
    some table.targetField else none

/-- Certify an authored plan by ordering it. A forward read left after ordering can only wait on or
close a cycle; a row table the scalar evaluator cannot run is refused once the order stands. -/
def certifyRepeatableNumberPlan (steps : List (CheckedNumericComputationTable model)) :
    Except RepeatableNumberPlanError (CheckedRepeatableNumberPlan model) :=
  if steps.isEmpty then .error .empty else
  match hDuplicate : FieldId.firstDuplicate? (steps.map (·.targetField)) with
  | some target => .error (.duplicateTarget target)
  | none =>
      match hForward : firstForwardComputationDependency?
          CheckedNumericComputationTable.targetField
          CheckedNumericComputationTable.referencesField
          (computationAuthoredOrder CheckedNumericComputationTable.targetField
            CheckedNumericComputationTable.referencesField steps.length steps) with
      | some (step, reads) => .error (.cycle step reads)
      | none =>
        match steps.findSome? rowTableNotScalar? with
        | some target => .error (.rowTableNotScalar target)
        | none => .ok {
            authored := steps
            execution := _
            executionOrdered := rfl
            uniqueTargets := hDuplicate
            dependenciesOrdered := hForward
          }

/-- A structural failure, with the target of the step that raised it. -/
inductive RepeatableNumberPlanFault where
  /-- A row's address or the target's row environments are structurally incoherent. -/
  | row (target : FieldId) (cause : AddressedNumericLeafFault)
  | table (target : FieldId) (cause : NumericComputationFault)
  | tableTargetCheck (target : FieldId) (cause : NumericTargetCheckFault)
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

private def supportedOutcome (table : CheckedNumericComputationTable model) :
    Except NumericComputationFault NumericTargetCheckResult →
      Except RepeatableNumberPlanFault NumericTargetOutcome
  | .error cause => throw (.table table.targetField cause)
  | .ok (.supported outcome) => pure outcome
  | .ok (.unsupported cause) => throw (.tableTargetCheck table.targetField cause)

private def executeFixed (table : CheckedNumericComputationTable model) (world : World)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except RepeatableNumberPlanFault (SourcedNumericTargetOutcome CellAddr) := do
  let outcome ← supportedOutcome table <| table.evaluateIn {
      scalar := { read := cellAt input read [], world := some world }
      document := input.source.toDocument
      outer := []
      filterRead := cellAt input read
      starRead := cellAt input read
    }
  let target : CellAddr := { field := table.targetField, path := [] }
  pure { targetField := target, outcome, source := input.numericTargetPlacementStateAt target }

/-- Run a table at a repeatable target once per row of its scope. A row selects and evaluates through
a context reading every field at its own scope under the row, so a field of the row reads that row's
cell and a field above it the enclosing one. An over-limit row clears without reading a guard. -/
private def executeRows (table : CheckedNumericComputationTable model) (world : World)
    (input : CheckedDocument model)
    (read : CellAddr → Except CheckedDocumentError CheckedCell) :
    Except RepeatableNumberPlanFault (List (SourcedNumericTargetOutcome CellAddr)) :=
  let scope := table.readingScope
  let addressAt (environment : Env) : Except RepeatableNumberPlanFault CellAddr := do
    let path ← (environment.pathForScope scope).mapError (.row table.targetField ∘ .environment)
    pure { field := table.targetField, path }
  input.computationRowOutcomes scope (.row table.targetField ∘ .targetRows)
    (fun environment => do
      let target ← addressAt environment
      pure { targetField := target, outcome := .noValue
             source := input.numericTargetPlacementStateAt target })
    (fun environment => do
      let target ← addressAt environment
      let outcome ← supportedOutcome table <|
        table.evaluate { read := cellAt input read environment, world := some world }
      pure { targetField := target, outcome, source := input.numericTargetPlacementStateAt target })

def executeSteps (plan : CheckedRepeatableNumberPlan model) (world : World)
    (input : CheckedDocument model) :
    List (CheckedNumericComputationTable model) →
      List (SourcedNumericTargetOutcome CellAddr) →
      Except RepeatableNumberPlanFault (List (SourcedNumericTargetOutcome CellAddr))
  | [], completed => pure completed
  | table :: remaining, completed => do
      let read := plan.read input completed
      let outcomes ←
        if table.readingScope.isEmpty then
          (fun outcome => [outcome]) <$> executeFixed table world input read
        else executeRows table world input read
      plan.executeSteps world input remaining (completed ++ outcomes)

/-- Run the certified order and return every outcome, grouped by step in that order and by row
within a step. -/
def execute (plan : CheckedRepeatableNumberPlan model) (world : World)
    (input : CheckedDocument model) :
    Except RepeatableNumberPlanFault (List (SourcedNumericTargetOutcome CellAddr)) :=
  plan.executeSteps world input plan.execution []

end CheckedRepeatableNumberPlan

end A12Kernel
